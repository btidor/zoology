#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
import json
from collections import defaultdict
from time import sleep
from typing import Dict, Iterable, List, Optional, Tuple

from arrays import FrozenBytes
from environment import Block, Contract, Transaction, Universe
from rpc import get_code, get_storage_at
from sha3 import SHA3, NarrowingError
from smt import Constraint, Uint160, Uint256
from solidity import abiencode
from solver import Solver
from state import Descend, Jump, State, Termination
from universal import _universal_transaction, symbolic_start
from vm import concrete_start, step

with open("ethernaut.json") as f:
    data = json.load(f)
    LEVEL_FACTORIES = [
        Uint160(int.from_bytes(bytes.fromhex(data[str(i)][2:]))) for i in range(29)
    ]


SETUP = Uint160(0x5757575757575757575757575757575757575757)
PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


class History:
    """Encapsulates a linear sequence of transactions."""

    def __init__(self, starting_universe: Universe, starting_sha3: SHA3) -> None:
        """Create a new History."""
        self.starting_universe = starting_universe
        self.starting_sha3 = starting_sha3
        self.states: List[State] = []

    def subsequent(self) -> Tuple[Universe, SHA3]:
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
        assert solver.check()

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        for state in self.states:
            state.narrow(solver)
            state.sha3.narrow(solver)
        assert solver.check()

    def describe(self, *constraints: Constraint) -> Iterable[str]:
        """Yield a human-readable description of the transaction sequence."""
        solver = Solver()
        for constraint in constraints:
            solver.assert_and_track(constraint)
        try:
            self.constrain(solver)
        except AssertionError:
            yield "unprintable: unsatisfiable"
            return

        try:
            for state in self.states:
                state.narrow(solver)
                state.sha3.narrow(solver)
        except NarrowingError:
            yield "unprintable: narrowing error"
            solver = Solver()
            for constraint in constraints:
                solver.assert_and_track(constraint)
            self.constrain(solver)
            for state in self.states:
                state.narrow(solver)

        for state in self.states:
            data = state.transaction.calldata.describe(solver, True)
            if len(data) == 0:
                data = "(empty) "
            elif len(data) > 8:
                data = data[:8] + " " + data[8:]
            line = f"{data}"

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


def create(factory: Contract) -> Tuple[Uint160, History]:
    """Call createInstance to set up the level."""
    calldata = abiencode("createInstance(address)") + PLAYER.into(Uint256).unwrap(bytes)
    contracts: Dict[int, Contract] = {}

    while True:
        # Caveat: this *concrete* universe will be used in symbolic execution
        # later. Any oversights in the environment (e.g. the player's address
        # having a zero balance, etc.) can result in inaccurate analysis.
        start = concrete_start(copy.deepcopy(factory), Uint256(0), calldata)
        start.transaction = Transaction(
            origin=SETUP,
            caller=SETUP,
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(calldata),
            gasprice=Uint256(0x12),
        )
        for contract in contracts.values():
            start.universe.add_contract(copy.deepcopy(contract))
        start.universe.balances[PLAYER] = Uint256(10**9)
        start.block = block(0, start.universe)

        end, accessed = execute(start)
        assert isinstance(end.pc, Termination)
        if end.pc.success is True:
            break

        for addr, keys in accessed.items():
            if addr == 0x70D070D070D070D070D070D070D070D070D070D0:
                continue
            if addr not in contracts:
                contracts[addr] = get_code(Uint160(addr))
            contract = contracts[addr]
            for key in keys:
                if key.unwrap() not in contract.storage.surface:
                    val = get_storage_at(Uint160(addr), key)
                    sleep(0.25)
                    contract.storage.poke(key, val)

    end.universe.add_contract(end.contract)
    address = Uint160(int.from_bytes(end.pc.returndata.unwrap()))
    return address, History(end.universe, end.sha3)


def validate(
    factory: Uint160, instance: Uint160, history: History, prints: bool = False
) -> Constraint:
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

    constraints = []
    for end in _universal_transaction(start, prints=prints):
        assert isinstance(end.pc, Termination)
        constraints.append(Uint256(end.pc.returndata._bigvector(32)) != Uint256(0))
    return Constraint.any(*constraints)


def execute(
    state: State, indent: Optional[int] = None
) -> Tuple[State, Dict[int, List[Uint256]]]:
    """Concretely execute a contract, tracking storage accesses."""
    accessed: Dict[int, List[Uint256]] = defaultdict(list)

    while isinstance(state.pc, int):
        instr = state.contract.program.instructions[state.pc]
        if indent is not None:
            print("." * indent, instr)

        match step(state):
            case None:
                pass
            case Jump(targets):
                matched = [
                    s for (c, s) in targets if c.unwrap("JUMPI requires concrete b")
                ]
                assert len(matched) == 1, "no matching jump target"
                state = matched[0]
            case Descend(substate, callback):
                substate, subaccessed = execute(
                    substate, indent + 2 if indent is not None else None
                )
                for s, v in subaccessed.items():
                    accessed[s].extend(v)
                state = callback(state, substate)
            case unknown:
                raise ValueError(f"unknown action: {unknown}")

        if indent is not None:
            for y in reversed(state.stack):
                print("." * indent, " ", y.describe())

    for contract in state.universe.contracts.values():
        accessed[contract.address.unwrap()].extend(contract.storage.accessed)
    accessed[state.contract.address.unwrap()].extend(state.contract.storage.accessed)
    return state, accessed


def search(
    address: Uint160, beginning: History, prints: bool = False
) -> Optional[History]:
    """Symbolically execute the given level until a solution is found."""
    histories: List[History] = [beginning]
    for i in range(16):
        suffix = str(i + 1)
        if prints:
            print(f"\tTxn {suffix}:")
        subsequent: List[History] = []
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
                    if "unsatisfiable" in output:
                        continue

                solver = Solver()
                candidate.constrain(solver)

                ok = validate(factory.address, address, candidate)
                if solver.check(ok):
                    solver.assert_and_track(ok)
                    assert solver.check()

                    try:
                        candidate.narrow(solver)
                        if prints:
                            print("  [found solution!]")
                        return candidate
                    except NarrowingError:
                        solver = Solver()
                        candidate.constrain(solver)

                try:
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

    for i in args.level:
        address = LEVEL_FACTORIES[i]
        print(f"{i:04}", end="")
        try:
            factory = get_code(address)
            address, beginning = create(factory)

            ok = validate(factory.address, address, beginning)
            assert ok.unwrap() is False

            solution = search(address, beginning, prints=(args.verbose > 1))
            if solution is None:
                print("\tno solution")
                continue

            ok = validate(factory.address, address, solution)
            for line in solution.describe(ok):
                print("\t" + line)

        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"\t{e.__class__.__name__}{suffix}")
            if args.verbose > 0:
                raise e
