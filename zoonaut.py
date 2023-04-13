#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
from typing import Iterable, Iterator

from arrays import Array, FrozenBytes, MutableBytes
from environment import Block, Transaction, Universe
from sha3 import SHA3
from smt import Constraint, Uint160, Uint256
from snapshot import LEVEL_FACTORIES, apply_snapshot
from solidity import abiencode
from solver import ConstrainingError, NarrowingError, Solver
from state import State, Termination
from universal import _universal_transaction, symbolic_start
from vm import concrete_start, printable_execution

SETUP = Uint160(0x5757575757575757575757575757575757575757)
PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


class History:
    """Encapsulates a linear sequence of transactions."""

    def __init__(self, starting_universe: Universe, starting_sha3: SHA3) -> None:
        """Create a new History."""
        self.starting_universe = starting_universe
        self.starting_sha3 = starting_sha3
        self.states: list[State] = []

    def subsequent(self) -> tuple[Universe, SHA3]:
        """Set up the execution of a new transaction."""
        if len(self.states) == 0:
            pair = (self.starting_universe, self.starting_sha3)
        else:
            pair = (self.states[-1].universe, self.states[-1].sha3)
        return copy.deepcopy(pair)

    def extend(self, state: State) -> History:
        """Add a new transaction to the History."""
        other = copy.deepcopy(self)
        other.states.append(state)
        return other

    def constrain(self, solver: Solver) -> None:
        """Apply hard constraints to the given solver instance."""
        for state in self.states:
            state.constrain(solver)
        if not solver.check():
            raise ConstrainingError

    def narrow(self, solver: Solver, skip_sha3: bool = False) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        if not skip_sha3:
            if len(self.states) > 0:
                self.states[-1].sha3.narrow(solver)
            else:
                self.starting_sha3.narrow(solver)

        for state in self.states:
            state.narrow(solver)

    def describe(
        self, *constraints: Constraint, skip_final: bool = False
    ) -> Iterable[str]:
        """Yield a human-readable description of the transaction sequence."""
        solver = Solver()
        for constraint in constraints:
            solver.assert_and_track(constraint)
        try:
            self.constrain(solver)
        except ConstrainingError:
            yield "unprintable: unsatisfiable"
            return

        try:
            self.narrow(solver)
        except NarrowingError:
            yield "unprintable: narrowing error"
            solver = Solver()
            for constraint in constraints:
                solver.assert_and_track(constraint)
            self.constrain(solver)
            self.narrow(solver, skip_sha3=True)

        states = self.states
        if skip_final:
            states = states[:-1]
        for state in states:
            data = state.transaction.calldata.describe(solver, True)
            if len(data) == 0:
                data = "(empty) "
            elif len(data) > 8:
                data = data[:8] + " " + data[8:]
            line = f"{state.px()}\t{data}"

            suffixes = []
            value = solver.evaluate(state.transaction.callvalue, True).unwrap()
            if value > 0:
                suffixes.append(f"value: {value}")
            caller = solver.evaluate(state.transaction.caller, True)
            if (caller != PLAYER).unwrap():
                suffixes.append(f"via proxy")
            if len(suffixes) > 0:
                line += f"\t({', '.join(suffixes)})"

            yield line


def block(offset: int, universe: Universe) -> Block:
    """Create a simulated Block."""
    # As an approximation, assume the blockhash of the `n`th block is
    # `999999*n`.
    number = Uint256(16030969 + offset)
    universe.blockhashes[number] = Uint256(999999) * number
    return Block(
        number=number,
        coinbase=Uint160(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5),
        timestamp=Uint256(1669214471 + offset),
        prevrandao=Uint256(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        ),
        gaslimit=Uint256(30000000000000000),
        chainid=Uint256(1),
        basefee=Uint256(12267131109),
    )


def create(universe: Universe, address: Uint160) -> tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    # Warning: this symbolic universe will be used in symbolic execution later
    # on. Inaccuracies in the environment may result in an inaccurate analysis.
    calldata = abiencode("createInstance(address)") + PLAYER.into(Uint256).unwrap(bytes)
    start = State(
        suffix="",
        block=block(0, universe),
        contract=universe.contracts[address.unwrap()],
        transaction=Transaction(
            origin=SETUP,
            caller=SETUP,
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(calldata),
            gasprice=Uint256(0x12),
        ),
        universe=universe,
        sha3=SHA3(),
        pc=0,
        stack=[],
        memory=MutableBytes.concrete(b""),
        children=0,
        latest_return=FrozenBytes.concrete(b""),
        logs=[],
        gas_variables=None,
        call_variables=[],
        path_constraints=[],
        path=1,
    )

    generator = printable_execution(start)
    try:
        while True:
            next(generator)
    except StopIteration as e:
        end = e.value
        assert isinstance(end, State)

    assert isinstance(end.pc, Termination)
    assert end.pc.success

    end.universe.add_contract(end.contract)
    address = Uint160(int.from_bytes(end.pc.returndata.unwrap()))
    return address, History(end.universe, end.sha3)


def validate(
    factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Iterator[tuple[State, Constraint]]:
    """Call validateInstance to check the solution."""
    calldata = (
        abiencode("validateInstance(address,address)")
        + instance.into(Uint256).unwrap(bytes)
        + PLAYER.into(Uint256).unwrap(bytes)
    )

    universe, sha3 = history.subsequent()
    contract = universe.contracts[factory.unwrap()]
    start = concrete_start(contract, Uint256(0), calldata)
    start.transaction = Transaction(
        origin=SETUP,
        caller=SETUP,
        callvalue=Uint256(0),
        calldata=FrozenBytes.concrete(calldata),
        gasprice=Uint256(0x12),
    )
    start.universe = universe
    start.sha3 = sha3

    for end in _universal_transaction(start, prints=prints):
        assert isinstance(end.pc, Termination)
        ok = Uint256(end.pc.returndata._bigvector(32)) != Uint256(0)
        yield (end, ok)


def search(
    address: Uint160, beginning: History, prints: bool = False
) -> tuple[History, Constraint] | None:
    """Symbolically execute the given level until a solution is found."""
    histories: list[History] = [beginning]
    for i in range(16):
        suffix = str(i + 1)
        if prints:
            print(f"\tTxn {suffix}:")
        subsequent: list[History] = []
        for history in histories:
            universe, sha3 = history.subsequent()
            instance = universe.contracts[address.unwrap()]
            start = symbolic_start(instance, sha3, suffix)
            start.universe = universe

            # ASSUMPTION: each call to the level takes place in a different
            # block, and the blocks are consecutive.
            start.block = block(i + 1, start.universe)

            # ASSUMPTION: all transactions are originated by the player, but may
            # (or may not!) be bounced through a "proxy" contract
            start.transaction = Transaction(
                origin=PLAYER,
                caller=Constraint(f"CALLERAB{suffix}").ite(PLAYER, PROXY),
                callvalue=Uint256(f"CALLVALUE{suffix}"),
                calldata=FrozenBytes.symbolic(f"CALLDATA{suffix}"),
                gasprice=Uint256(f"GASPRICE{suffix}"),
            )
            start.universe.transfer(
                start.transaction.origin,
                start.contract.address,
                start.transaction.callvalue,
            )
            start.contract.storage.written = []

            for end in _universal_transaction(start):
                candidate = history.extend(end)

                if prints:
                    sp = "-"
                    output = ""
                    for line in candidate.describe():
                        output += f"{sp} {line}\n"
                        sp = " "
                    print(output, end="")

                for post, ok in validate(address, address, candidate):
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
    parser.add_argument("-v", "--verbose", action="count", default=0)
    args = parser.parse_args()
    if args.level is None:
        args.level = list(range(len(LEVEL_FACTORIES)))

    with open("snapshot.json", "r") as f:
        universe = Universe(
            suffix="",
            balances=Array.symbolic(f"BALANCE", Uint160, Uint256),
            transfer_constraints=[],
            contracts={},
            codesizes=Array.symbolic(f"CODESIZE", Uint160, Uint256),
            blockhashes=Array.symbolic(f"BLOCKHASH", Uint256, Uint256),
            # We're not using the goal feature:
            agents=[],
            contribution=Uint256(f"CONTRIBUTION"),
            extraction=Uint256(f"EXTRACTION"),
        )
        apply_snapshot(f, universe)

    for i in args.level:
        if i == 0:
            continue
        factory = LEVEL_FACTORIES[i]
        print(f"{i:04}", end="")
        try:
            instance, beginning = create(copy.deepcopy(universe), factory)

            for _, ok in validate(factory, instance, beginning):
                assert ok.unwrap() is False

            result = search(instance, beginning, prints=(args.verbose > 1))
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
