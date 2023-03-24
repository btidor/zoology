#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
import json
from collections import defaultdict
from time import sleep
from typing import Dict, List, Optional, Tuple

from arrays import FrozenBytes
from environment import Block, Contract, Transaction, Universe
from rpc import get_code, get_storage_at
from sha3 import SHA3
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


def create(factory: Contract) -> Tuple[Uint160, Universe]:
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
    return address, end.universe


def validate(factory: Uint160, instance: Uint160, universe: Universe) -> Constraint:
    """Call validateInstance to check the solution."""
    calldata = (
        abiencode("validateInstance(address,address)")
        + instance.into(Uint256).unwrap(bytes)
        + PLAYER.into(Uint256).unwrap(bytes)
    )

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

    return Constraint.any(
        *(
            (Uint256(end.pc.returndata._bigvector()) != Uint256(0))
            for end in _universal_transaction(start)
            if isinstance(end.pc, Termination)  # should always be true
        )
    )


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
    address: Uint160, starting_universe: Universe, prints: bool = False
) -> Optional[List[State]]:
    """Symbolically execute the given level until a solution is found."""
    sha3 = SHA3()
    histories: List[List[State]] = [[]]
    for i in range(16):
        suffix = str(i)
        if prints:
            print(f"Level {suffix}:")
        subsequent: List[List[State]] = []
        for history in histories:
            if len(history) > 0:
                universe = history[-1].universe
            else:
                universe = starting_universe
            universe = copy.deepcopy(universe)

            instance = universe.contracts[address.unwrap()]
            start = symbolic_start(instance, sha3, suffix)
            start.universe = universe

            # ASSUMPTION: each call to the level takes place in a different
            # block, and the blocks are consecutive.
            start.block = block(i + 1, start.universe)

            # ASSUMPTION: origin and caller are the player's fixed address
            start.transaction = Transaction(
                origin=PLAYER,
                caller=PLAYER,
                callvalue=Uint256(f"CALLVALUE{suffix}"),
                calldata=FrozenBytes.symbolic(f"CALLDATA{suffix}"),
                gasprice=Uint256(f"GASPRICE{suffix}"),
            )
            start.universe.transfer(
                start.transaction.caller,
                start.contract.address,
                start.transaction.callvalue,
            )
            start.contract.storage.written = []

            for end in _universal_transaction(start):
                states = history + [end]

                solver = Solver()
                for state in states:
                    state.constrain(solver)
                assert solver.check()

                sp = "-"
                for state in states:
                    state.narrow(solver)
                    if prints:
                        data = state.transaction.calldata.evaluate(solver, True)
                        if len(data) == 0:
                            data = "(empty)"
                        value = solver.evaluate(state.transaction.callvalue, True)
                        print(f"{sp} {data}\t(value: {value.unwrap()})")
                    sp = " "

                solver = Solver()
                for state in states:
                    state.constrain(solver)
                assert solver.check()

                ok = validate(factory.address, address, states[-1].universe)
                if solver.check(ok):
                    if prints:
                        print("  [found solution!]")
                    return states

                if len(end.contract.storage.written) == 0:
                    # TODO: check if *any* contract's storage was written; also
                    # note that this ignores transactions that only change
                    # contract balances, which can also be material
                    if prints:
                        print("  [read-only]")
                    continue

                if prints:
                    print("  [candidate]")
                subsequent.append(states)

        histories = subsequent
        assert len(histories) < 256

    return None


if __name__ == "__main__":
    for i, address in enumerate(LEVEL_FACTORIES):
        print(f"{i:04}", end="")
        try:
            factory = get_code(address)
            address, universe = create(factory)

            ok = validate(factory.address, address, universe)
            assert ok.unwrap() is False

            solution = search(address, universe)
            if solution is None:
                print("\tno solution")
                continue

            for state in solution:
                solver = Solver()
                state.constrain(solver)
                assert solver.check()

                state.narrow(solver)
                data = state.transaction.calldata.evaluate(solver, True)
                if len(data) == 0:
                    data = "(empty)"
                value = solver.evaluate(state.transaction.callvalue, True)
                print(f"\t{data}\t(value: {value.unwrap()})")

        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"\t{e.__class__.__name__}{suffix}")
