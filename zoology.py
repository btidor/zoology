#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy

from disassembler import abiencode
from environment import Block, Contract, Transaction, Universe
from history import History, Validator
from smt.arrays import Array
from smt.bytes import FrozenBytes
from smt.sha3 import SHA3
from smt.smt import Constraint, Uint160, Uint256
from smt.solver import ConstrainingError, NarrowingError, Solver
from snapshot import LEVEL_FACTORIES, apply_snapshot
from state import State, Termination
from universal import symbolic_start, universal_transaction
from vm import printable_execution

SETUP = Uint160(0x5757575757575757575757575757575757575757)
PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


def starting_universe() -> Universe:
    """Set up a symbolic universe with factory levels loaded."""
    universe = Universe.symbolic("")
    universe.codesizes.poke(SETUP, Uint256(0))
    universe.codesizes.poke(PLAYER, Uint256(0))
    apply_snapshot(universe)
    return universe


def createInstance(
    universe: Universe, address: Uint160, prints: bool = False
) -> tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    # Warning: this symbolic universe will be used in symbolic execution later
    # on. Inaccuracies in the environment may result in an inaccurate analysis.
    assert (p := PLAYER.reveal()) is not None
    calldata = abiencode("createInstance(address)") + p.to_bytes(32)
    assert (a := address.reveal()) is not None
    start = State(
        block=Block(),
        contract=universe.contracts[a],
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            calldata=FrozenBytes.concrete(calldata),
            callvalue=Uint256(10**15),
        ),
        universe=universe,
    )
    start.transfer(
        start.transaction.caller, start.contract.address, start.transaction.callvalue
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

    end.universe.add_contract(end.contract)
    assert (data := end.pc.returndata.reveal()) is not None
    return Uint160(int.from_bytes(data)), History(end.universe, end.sha3, PLAYER)


def validateInstance(
    _factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Validator | None:
    """Symbolically interpret validateInstance as a function, if possible."""
    assert (factory := _factory.reveal()) is not None

    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    sha3 = SHA3()
    universe, _, _ = history.subsequent()
    contract = universe.contracts[factory]
    start = symbolic_start(contract, sha3, "")
    start.transaction = Transaction(
        origin=SETUP,
        caller=SETUP,
        calldata=FrozenBytes.concrete(calldata),
    )

    for reference in universe.contracts.values():
        assert (a := reference.address.reveal()) is not None
        start.universe.add_contract(
            Contract(
                address=reference.address,
                program=reference.program,
                storage=Array.symbolic(
                    f"STORAGE@{a.to_bytes(20).hex()}", Uint256, Uint256
                ),
                nonce=reference.nonce,
            )
        )

    predicates: list[Constraint] = []
    for end in universal_transaction(start, check=False, prints=prints):
        assert isinstance(end.pc, Termination)

        # This logic needs to match State.constrain()
        predicates.append(
            Constraint.all(
                end.constraint,
                Uint256(end.pc.returndata.bigvector(32)) != Uint256(0),
            )
        )

    assert predicates
    if sha3.constraints:
        # We can't currently handle feeding the global SHA3 instance into the
        # validator. Fall back to running validateInstance with concrete inputs
        # at every step.
        return None
    try:
        # Eligible for validator optimization!
        return Validator(Constraint.any(*predicates))
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
        solver.assert_and_track(validator.translate(history))
        return solver

    assert (factory := _factory.reveal()) is not None

    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    universe, sha3, block = history.subsequent()
    contract = universe.contracts[factory]
    start = symbolic_start(contract, sha3, "")
    start.transaction = Transaction(
        origin=SETUP,
        caller=SETUP,
        calldata=FrozenBytes.concrete(calldata),
    )
    start.universe = universe
    start.block = block

    for end in universal_transaction(start):
        assert isinstance(end.pc, Termination)
        solver = Solver()
        candidate = history.extend(end)
        candidate.constrain(solver, check=False)
        ok = Uint256(end.pc.returndata.bigvector(32)) != Uint256(0)
        solver.assert_and_track(ok)
        if solver.check():
            end.sha3.narrow(solver)
            return solver

    solver = Solver()
    solver.assert_and_track(Constraint(False))
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

    histories: list[History] = [beginning]
    for i in range(depth):
        suffix = str(i + 1)
        if verbose > 1:
            print(f"\tTxn {suffix}:")
        subsequent: list[History] = []
        for history in histories:
            universe, sha3, block = history.subsequent()
            contract = universe.contracts[instance]
            start = symbolic_start(contract, sha3, suffix)
            start.universe = universe

            # ASSUMPTION: each call to the level takes place in a different
            # block, and the blocks are consecutive.
            start.block = block

            # ASSUMPTION: all transactions are originated by the player, but may
            # (or may not!) be bounced through a "proxy" contract
            start.transaction = Transaction.symbolic(
                suffix=suffix,
                origin=PLAYER,
                caller=Constraint(f"CALLERAB{suffix}").ite(PLAYER, PROXY),
            )
            start.transfer(
                start.transaction.origin,
                start.contract.address,
                start.transaction.callvalue,
            )
            start.contract.storage.written = []

            for end in universal_transaction(start, prints=(verbose > 2)):
                candidate = history.extend(end)
                if verbose > 1:
                    try:
                        solver = Solver()
                        candidate.constrain(solver)
                        candidate.narrow(solver)
                        sp = "-"
                        output = ""
                        for line in candidate.describe(solver):
                            output += f"{sp} {line}\n"
                            sp = " "
                        print(output, end="")
                    except ConstrainingError:
                        print(f"- [{candidate.pxs()}] unprintable: unsatisfiable")
                        continue
                    except NarrowingError:
                        print(f"- [{candidate.pxs()}] unprintable: narrowing error")
                        continue

                solver = constrainWithValidator(
                    factory, _instance, candidate, validator
                )
                candidate.constrain(solver, check=False)
                if solver.check():
                    candidate.narrow(solver)
                    if verbose > 1:
                        print("  [found solution!]")
                    return candidate, solver

                if len(end.contract.storage.written) == 0:
                    # TODO: check if *any* contract's storage was written; also
                    # note that this ignores transactions that only change
                    # contract balances, which can also be material
                    if verbose > 1:
                        print("  [read-only]")
                    continue

                try:
                    solver = Solver()
                    candidate.constrain(solver)
                except ConstrainingError:
                    if verbose > 1:
                        print("  [constraining error]")
                    continue

                if verbose > 1:
                    print("  [candidate]")
                subsequent.append(candidate)

        histories = subsequent

    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-l", "--level", help="select which level(s) to run", action="append", type=int
    )
    parser.add_argument(
        "-d", "--depth", help="maximum number of transactions", type=int, default=4
    )
    parser.add_argument("-v", "--verbose", action="count", default=0)
    args = parser.parse_args()
    if args.level is None:
        args.level = list(range(len(LEVEL_FACTORIES)))
    for i in args.level:
        if i < 0 or i >= len(LEVEL_FACTORIES):
            raise ValueError(f"invalid level: {i}")

    universe = starting_universe()

    for i in args.level:
        factory = LEVEL_FACTORIES[i]
        print(f"{i:04}", end="")
        try:
            instance, beginning = createInstance(
                copy.deepcopy(universe), factory, prints=(args.verbose > 2)
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
