#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
from functools import reduce
from itertools import chain

from bytes import Bytes
from disassembler import abiencode
from environment import Contract, Transaction, Universe
from history import History, Validator
from sha3 import SHA3
from smt import (
    Array,
    ConstrainingError,
    Constraint,
    NarrowingError,
    Solver,
    Uint64,
    Uint160,
    Uint256,
)
from snapshot import LEVEL_FACTORIES, apply_snapshot
from state import State, Termination
from universal import universal_transaction
from vm import printable_execution

SETUP = Uint160(0x5757575757575757575757575757575757575757)
PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


def starting_universe(factory: Uint160) -> Universe:
    """Set up a symbolic universe with factory levels loaded."""
    universe = Universe.symbolic("")
    universe.codesizes.poke(SETUP, Uint256(0))
    universe.codesizes.poke(PLAYER, Uint256(0))
    universe.codesizes.poke(Uint160(0xA9E), Uint256(0))  # burn address in lvl 20
    universe.gashog = Constraint("GASHOG").ite(PROXY, Uint160(0))
    apply_snapshot(universe, factory)
    return universe


def createInstance(
    universe: Universe, address: Uint160, prints: bool = False
) -> tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    # Warning: this symbolic universe will be used in symbolic execution later
    # on. Inaccuracies in the environment may result in an inaccurate analysis.
    assert (p := PLAYER.reveal()) is not None
    calldata = abiencode("createInstance(address)") + p.to_bytes(32)
    start = State(
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            address=address,
            calldata=Bytes(calldata),
            callvalue=Uint256(10**15),
        ),
        universe=universe,
    )
    start.transfer(
        start.transaction.caller, start.transaction.address, start.transaction.callvalue
    )

    generator = printable_execution(start)
    try:
        while True:
            line = next(generator)
            if prints:
                print(line)
    except StopIteration as e:
        end = e.value
        assert isinstance(end, State)

    assert isinstance(end.pc, Termination)
    assert (data := end.pc.returndata.reveal()) is not None
    error = data[68:].strip().decode()
    assert end.pc.success, f"createInstance() failed{': ' + error if error else ''}"
    return Uint160(int.from_bytes(data)), History(end.universe, end.sha3, PLAYER)


def validateInstance(
    _factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Validator | None:
    """Symbolically interpret validateInstance as a function, if possible."""
    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    universe, _, _ = history.subsequent()
    universe.balances = Array[Uint160, Uint256]("BALANCE")
    sha3 = SHA3()  # validatior optimization assumes no SHA3
    start = State(
        suffix="-V",
        block=history.validation_block(),
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            address=_factory,
            calldata=Bytes(calldata),
        ),
        universe=universe,
        sha3=sha3,
        gas_count=0,
    )

    for reference in universe.contracts.values():
        assert (a := reference.address.reveal()) is not None
        start = start.with_contract(
            Contract(
                address=reference.address,
                program=reference.program,
                storage=Array[Uint256, Uint256](f"STORAGE@{a.to_bytes(20).hex()}"),
                nonce=reference.nonce,
            ),
            True,
        )
    universe.codesizes.written = []

    predicates = list[Constraint]()
    for end in universal_transaction(start, check=False, prints=prints):
        assert isinstance(end.pc, Termination)

        # This logic needs to match State.constrain(). We don't need to worry
        # about narrowing because SHA3 is not invoked (see check below).
        b: Uint256 = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector()
        predicates.append(end.constraint & (b != Uint256(0)))

        if end.universe.codesizes.written:
            # We can't handle validators that create contracts, though that
            # would be pretty strange.
            return None

    assert predicates
    if sha3.free or sha3.symbolic:
        # We can't currently handle feeding the global SHA3 instance into the
        # validator. Fall back to running validateInstance with concrete inputs
        # at every step.
        return None
    try:
        # Eligible for validator optimization!
        return Validator(reduce(lambda p, q: p | q, predicates, Constraint(False)))
    except ValueError:
        # Validator expression uses an unsupported variable; fall back.
        return None


def constrainWithValidator(
    _factory: Uint160,
    instance: Uint160,
    history: History,
    validator: Validator | None,
) -> Solver:
    """Simulate the execution of validateInstance on the given history."""
    if validator is not None:
        solver = Solver()
        solver.add(validator.translate(history))
        return solver

    assert (factory := _factory.reveal()) is not None

    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    universe, sha3, _ = history.subsequent()
    start = State(
        suffix="-V",
        block=history.validation_block(),
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            address=Uint160(factory),
            calldata=Bytes(calldata),
        ),
        universe=universe,
        sha3=sha3,
        gas_count=0,
    )

    for end in universal_transaction(start):
        assert isinstance(end.pc, Termination)
        solver = Solver()
        candidate = history.extend(end)
        candidate.constrain(solver, check=False)
        ok = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector() != Uint256(0)
        solver.add(ok)
        if solver.check():
            end.sha3.narrow(solver)
            return solver

    solver = Solver()
    solver.add(Constraint(False))
    return solver


def search(
    factory: Uint160,
    _instance: Uint160,
    beginning: History,
    validator: Validator | None,
    depth: int,
    verbose: int = 0,
) -> tuple[History, Solver] | None:
    """Symbolically execute the given level until a solution is found."""
    assert (instance := _instance.reveal()) is not None

    histories = [beginning]
    for i in range(depth):
        suffix = f"@{i+1}"
        if verbose > 1:
            print(f"\tTxn {i+1}:")
        subsequent = list[History]()
        for history in histories:
            universe, sha3, block = history.subsequent()
            start = State(
                suffix=suffix,
                # ASSUMPTION: each call to the level takes place in a different
                # block, and the blocks are consecutive.
                block=block,
                transaction=Transaction(
                    address=Uint160(instance),
                    origin=PLAYER,
                    # ASSUMPTION: all transactions are originated by the player,
                    # but may (or may not!) be bounced through a "proxy"
                    # contract.
                    caller=Constraint(f"CALLERAB{suffix}").ite(PLAYER, PROXY),
                    # ASSUMPTION: each transaction sends less than ~18 ETH.
                    callvalue=Uint64(f"CALLVALUE{suffix}").into(Uint256),
                    calldata=Bytes.symbolic(f"CALLDATA{suffix}"),
                    gasprice=Uint256(f"GASPRICE{suffix}"),
                ),
                universe=universe,
                sha3=sha3,
                gas_count=0,
            )
            start.transfer(
                start.transaction.origin,
                start.transaction.address,
                start.transaction.callvalue,
            )

            # TODO: also consider SELFDESTRUCTing to other addresses
            selfdestruct = copy.deepcopy(start)

            universal = universal_transaction(start, check=False, prints=(verbose > 2))
            for end in chain(universal, [selfdestruct]):
                candidate = history.extend(end)
                if verbose > 1:
                    print(f"- {candidate.pz()}")
                    try:
                        solver = Solver()
                        candidate.constrain(solver)
                        candidate.narrow(solver)
                        for line in candidate.describe(solver):
                            print(f"  : {line}")
                    except ConstrainingError:
                        print("  ! constraining error")
                        continue
                    except NarrowingError:
                        print("  ! narrowing error")
                        continue

                solver = constrainWithValidator(
                    factory, _instance, candidate, validator
                )
                candidate.constrain(solver, check=False)
                if solver.check():
                    candidate.narrow(solver)
                    if verbose > 1:
                        print("  > found solution!")
                    return candidate, solver

                if all(
                    len(c.storage.written) == 0 for c in end.universe.contracts.values()
                ):
                    # TODO: this ignores transactions that only change contract
                    # balances, which can also be material
                    if verbose > 1:
                        print("  > read-only")
                    continue

                if not verbose > 1:
                    try:
                        solver = Solver()
                        candidate.constrain(solver)
                    except ConstrainingError:
                        if verbose > 1:
                            print("  ! constraining error")
                        continue

                if verbose > 1:
                    print("  > candidate")
                subsequent.append(candidate)

        histories = subsequent

    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-l", "--level", help="select which level(s) to run", action="append", type=int
    )
    parser.add_argument(
        "-d", "--depth", help="maximum number of transactions", type=int, default=10
    )
    parser.add_argument("-v", "--verbose", action="count", default=0)
    args = parser.parse_args()
    if args.level is None:
        args.level = list(range(len(LEVEL_FACTORIES)))
    for i in args.level:
        if i < 0 or i >= len(LEVEL_FACTORIES):
            raise ValueError(f"invalid level: {i}")

    for i in args.level:
        factory = LEVEL_FACTORIES[i]
        print(f"{i:04}", end="")
        try:
            universe = starting_universe(factory)
            instance, beginning = createInstance(
                universe, factory, prints=(args.verbose > 2)
            )
            validator = validateInstance(
                factory, instance, beginning, prints=(args.verbose > 2)
            )
            solver = constrainWithValidator(factory, instance, beginning, validator)
            assert not solver.check()

            result = search(
                factory,
                instance,
                beginning,
                validator,
                args.depth,
                verbose=args.verbose,
            )
            if result is None:
                print("\tno solution")
                continue

            solution, solver = result
            for line in solution.describe(solver):
                print("\t" + line)

        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"\t{e.__class__.__name__}{suffix}")
            if args.verbose > 0:
                raise e
