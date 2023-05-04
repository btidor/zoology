#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
from typing import Iterator

from disassembler import abiencode
from environment import Block, Transaction, Universe
from history import History
from smt.bytes import FrozenBytes
from smt.smt import Constraint, Uint160, Uint256
from smt.solver import NarrowingError, Solver
from snapshot import LEVEL_FACTORIES, apply_snapshot
from state import State, Termination
from universal import symbolic_start, universal_transaction
from vm import concrete_start, printable_execution

SETUP = Uint160(0x5757575757575757575757575757575757575757)
PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


def starting_universe() -> Universe:
    """Set up a symbolic universe with factory levels loaded."""
    universe = Universe.symbolic("")
    universe.codesizes.poke(PLAYER, Uint256(0))
    with open("snapshot.json", "r") as f:
        apply_snapshot(f, universe)
    return universe


def createInstance(universe: Universe, address: Uint160) -> tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    # Warning: this symbolic universe will be used in symbolic execution later
    # on. Inaccuracies in the environment may result in an inaccurate analysis.
    calldata = abiencode("createInstance(address)") + PLAYER.into(Uint256).unwrap(bytes)
    start = State(
        block=Block(),
        contract=universe.contracts[address.unwrap()],
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            calldata=FrozenBytes.concrete(calldata),
        ),
        universe=universe,
    )

    generator = printable_execution(start)
    try:
        while True:
            next(generator)
    except StopIteration as e:
        end = e.value
        assert isinstance(end, State)

    assert isinstance(end.pc, Termination)
    error = end.pc.returndata.unwrap()[68:].strip().decode()
    assert end.pc.success, f"createInstance() failed{': ' + error if error else ''}"

    end.universe.add_contract(end.contract)
    address = Uint160(int.from_bytes(end.pc.returndata.unwrap()))
    return address, History(end.universe, end.sha3, PLAYER)


def validateInstance(
    factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Iterator[tuple[State, Constraint]]:
    """Call validateInstance to check the solution."""
    calldata = (
        abiencode("validateInstance(address,address)")
        + instance.into(Uint256).unwrap(bytes)
        + PLAYER.into(Uint256).unwrap(bytes)
    )

    universe, sha3, block = history.subsequent()
    contract = universe.contracts[factory.unwrap()]
    start = concrete_start(contract, Uint256(0), calldata)
    start.block = block
    start.transaction = Transaction(
        origin=SETUP,
        caller=SETUP,
        calldata=FrozenBytes.concrete(calldata),
    )
    start.universe = universe
    start.sha3 = sha3

    for end in universal_transaction(start, prints=prints):
        assert isinstance(end.pc, Termination)
        ok = Uint256(end.pc.returndata.bigvector(32)) != Uint256(0)
        yield (end, ok)


def search(
    factory: Uint160,
    instance: Uint160,
    beginning: History,
    depth: int,
    prints: bool = False,
) -> tuple[History, Constraint] | None:
    """Symbolically execute the given level until a solution is found."""
    histories: list[History] = [beginning]
    for i in range(depth):
        suffix = str(i + 1)
        if prints:
            print(f"\tTxn {suffix}:")
        subsequent: list[History] = []
        for history in histories:
            universe, sha3, block = history.subsequent()
            contract = universe.contracts[instance.unwrap()]
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
            start.universe.transfer(
                start.transaction.origin,
                start.contract.address,
                start.transaction.callvalue,
            )
            start.contract.storage.written = []

            for end in universal_transaction(start):
                candidate = history.extend(end)

                if prints:
                    sp = "-"
                    output = ""
                    for line in candidate.describe():
                        output += f"{sp} {line}\n"
                        sp = " "
                    print(output, end="")

                for post, ok in validateInstance(factory, instance, candidate):
                    complete = candidate.extend(post)

                    solver = Solver()
                    complete.constrain(solver)
                    solver.assert_and_track(ok)

                    if not solver.check():
                        continue

                    try:
                        complete.narrow(solver)
                        if prints:
                            print("  [found solution!]")
                        return complete, ok
                    except NarrowingError:
                        continue

                try:
                    solver = Solver()
                    candidate.constrain(solver)
                    candidate.narrow(solver)
                except NarrowingError:
                    if prints:
                        print("  [narrowing error]")
                    continue

                if len(end.contract.storage.written) == 0:
                    # TODO: check if *any* contract's storage was written; also
                    # note that this ignores transactions that only change
                    # contract balances, which can also be material
                    if prints:
                        print("  [read-only]")
                    continue

                if prints:
                    print("  [candidate]")
                subsequent.append(candidate)

        histories = subsequent
        assert len(histories) < 256

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
            instance, beginning = createInstance(copy.deepcopy(universe), factory)
            for _, ok in validateInstance(factory, instance, beginning):
                assert ok.unwrap() is False

            result = search(
                factory, instance, beginning, args.depth, prints=(args.verbose > 1)
            )
            if result is None:
                print("\tno solution")
                continue

            solution, ok = result
            for line in solution.describe(ok, skip_final=True):
                print("\t" + line)

        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"\t{e.__class__.__name__}{suffix}")
            if args.verbose > 0:
                raise e
