#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
import sys
import time
from functools import reduce
from itertools import chain

from bytes import Bytes
from disassembler import abiencode
from environment import ConcreteContract, Contract, Transaction
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
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import State, Termination
from universal import universal_transaction
from vm import printable_execution

PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


def createInstance(
    contracts: dict[int, Contract], address: Uint160, prints: bool = False
) -> tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    assert (p := PLAYER.reveal()) is not None
    calldata = abiencode("createInstance(address)") + p.to_bytes(32)
    # ASSUMPTION: the only contracts in existence are the ones related to the
    # level factory. This means precompiled contracts are not available!
    start = State(
        transaction=Transaction(
            origin=PLAYER,
            caller=PLAYER,
            address=address,
            calldata=Bytes(calldata),
            callvalue=Uint256(10**15),
        ),
        contracts=contracts,
        mystery_proxy=PROXY,
    )
    # ASSUMPTION: the only account with a nonzero balance belongs to the player.
    start.balances[PLAYER] = Uint256(10**18)
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
    return Uint160(int.from_bytes(data)), History(
        end.contracts, end.balances, end.sha3, PLAYER
    )


def validateInstance(
    factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Validator | None:
    """Symbolically interpret validateInstance as a function, if possible."""
    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    contracts, _, _, _ = history.subsequent()
    balances = Array[Uint160, Uint256]("BALANCE")
    sha3 = SHA3()  # validatior optimization assumes no SHA3
    start = State(
        suffix="-V",
        block=history.validation_block(),
        transaction=Transaction(
            origin=PLAYER,
            caller=PLAYER,
            address=factory,
            calldata=Bytes(calldata),
        ),
        sha3=sha3,
        contracts=contracts,
        balances=balances,
        mystery_proxy=PROXY,
        gas_count=0,
    )

    for reference in contracts.values():
        assert (a := reference.address.reveal()) is not None
        assert isinstance(reference, ConcreteContract)
        start = start.with_contract(
            ConcreteContract(
                address=reference.address,
                program=reference.program,
                storage=Array[Uint256, Uint256](f"STORAGE@{a.to_bytes(20).hex()}"),
                nonce=reference.nonce,
            ),
            True,
        )

    predicates = list[Constraint]()
    for end in universal_transaction(start, check=False, prints=prints):
        assert isinstance(end.pc, Termination)

        # This logic needs to match State.constrain(). We don't need to worry
        # about narrowing because SHA3 is not invoked (see check below).
        b: Uint256 = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector()
        predicates.append(end.constraint & (b != Uint256(0)))

        if len(end.contracts) > len(contracts):
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
    factory: Uint160,
    instance: Uint160,
    history: History,
    validator: Validator | None,
) -> tuple[State | None, Solver]:
    """Simulate the execution of validateInstance on the given history."""
    if validator is not None:
        solver = Solver()
        solver.add(validator.translate(history))
        return None, solver

    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )

    contracts, balances, sha3, _ = history.subsequent()
    start = State(
        suffix="-V",
        block=history.validation_block(),
        transaction=Transaction(
            origin=PLAYER,
            caller=PLAYER,
            address=factory,
            calldata=Bytes(calldata),
        ),
        sha3=sha3,
        contracts=contracts,
        balances=balances,
        mystery_proxy=PROXY,
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
            return end, solver

    solver = Solver()
    solver.add(Constraint(False))
    return None, solver


def search(
    factory: Uint160,
    instance: Uint160,
    beginning: History,
    validator: Validator | None,
    depth: int,
    verbose: int = 0,
) -> tuple[History, Solver] | None:
    """Symbolically execute the given level until a solution is found."""
    histories = [beginning]
    for i in range(depth):
        suffix = f"@{i+1}"
        if verbose:
            print(f"\nTrans {i+1:02} | {int(time.time())-startux:06}")
        j = 0
        subsequent = list[History]()
        for history in histories:
            contracts, balances, sha3, block = history.subsequent()
            start = State(
                suffix=suffix,
                # ASSUMPTION: each call to the level takes place in a different
                # block, and the blocks are consecutive.
                block=block,
                transaction=Transaction(
                    address=instance,
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
                sha3=sha3,
                contracts=contracts,
                balances=balances,
                mystery_proxy=PROXY,
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
                if verbose == 1:
                    if j > 0 and j % 16 == 0:
                        print()
                    vprint(f"{j:04x} ")
                j += 1

                candidate = history.extend(end)
                if verbose > 1:
                    print(f"- {candidate.pz()}")
                    try:
                        solver = Solver()
                        candidate.constrain(solver)
                        candidate.narrow(solver)
                        newline = True
                        for part in candidate.describe(solver):
                            if newline:
                                print("  : ", end="")
                                newline = False
                            print(part, end="")
                            if part.endswith("\n"):
                                newline = True
                            sys.stdout.flush()
                    except ConstrainingError:
                        print("  ! constraining error")
                        continue
                    except NarrowingError:
                        print("  ! narrowing error")
                        continue

                final, solver = constrainWithValidator(
                    factory, instance, candidate, validator
                )
                candidate.constrain(solver, check=False)
                if solver.check():
                    candidate.narrow(solver)
                    if verbose > 1:
                        print("  > found solution!")
                    else:
                        vprint("# ")
                    return candidate.with_final(final), solver

                if all(len(c.storage.written) == 0 for c in end.contracts.values()):
                    # TODO: this ignores transactions that only change contract
                    # balances, which can also be material
                    if verbose > 1:
                        print("  > read-only")
                    else:
                        vprint(". ")
                    continue

                if not verbose > 1:
                    try:
                        solver = Solver()
                        candidate.constrain(solver)
                    except ConstrainingError:
                        vprint("! ")
                        continue

                if verbose > 1:
                    print("  > candidate")
                else:
                    vprint("* ")
                subsequent.append(candidate)

        histories = subsequent

    return None


def vprint(part: str) -> None:
    """Print a partial line, if verbose mode is enabled."""
    if "args" in globals() and args.verbose:
        print(part, end="")
        sys.stdout.flush()


if __name__ == "__main__":
    startux = int(time.time())
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
        vprint(f"Level {i:02}  [U")
        try:
            contracts = snapshot_contracts(factory)
            vprint("R")
            instance, beginning = createInstance(
                contracts, factory, prints=(args.verbose > 2)
            )
            vprint("V")
            validator = validateInstance(
                factory, instance, beginning, prints=(args.verbose > 2)
            )
            vprint("S")
            _, solver = constrainWithValidator(factory, instance, beginning, validator)
            vprint("C")
            assert not solver.check()
            vprint("]")

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
            newline = True
            print(f"\nResult   | {int(time.time())-startux:06}")
            for part in solution.describe(solver):
                if newline:
                    print("  ", end="")
                    newline = False
                print(part, end="")
                if part.endswith("\n"):
                    newline = True

        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"\t{e.__class__.__name__}{suffix}")
            if args.verbose:
                raise e
