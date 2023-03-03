#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
import json
from collections import defaultdict
from time import sleep
from typing import Dict, List, Optional, Tuple

from arrays import FrozenBytes
from environment import Contract, Transaction, Universe
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


def create(factory: Contract) -> Tuple[Uint160, Universe]:
    """Call createInstance to set up the level."""
    calldata = abiencode("createInstance(address)") + PLAYER.into(Uint256).unwrap(bytes)
    contracts: Dict[int, Contract] = {}

    while True:
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

        end, accessed = _execute(start)
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


def _execute(
    state: State, indent: Optional[int] = None
) -> Tuple[State, Dict[int, List[Uint256]]]:
    accessed: Dict[int, List[Uint256]] = defaultdict(list)

    while isinstance(state.pc, int):
        instr = state.contract.program.instructions[state.pc]
        if indent is not None:
            print("." * indent, instr)

        match step(state):
            case None:
                continue
            case Jump(targets):
                matched = [
                    s for (c, s) in targets if c.unwrap("JUMPI requires concrete b")
                ]
                assert len(matched) == 1, "no matching jump target"
                state = matched[0]
            case Descend(substate, callback):
                substate, subaccessed = _execute(
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


if __name__ == "__main__":
    for i, address in enumerate(LEVEL_FACTORIES):
        print(f"{i:04}", end="\t")
        try:
            factory = get_code(address)
            address, universe = create(factory)

            ok = validate(factory.address, address, universe)

            instance = universe.contracts[address.unwrap()]
            start = symbolic_start(instance, SHA3(), "")
            start.universe = universe
            start.universe.transfer(
                start.transaction.caller,
                start.contract.address,
                start.transaction.callvalue,
            )

            solution = None
            for end in _universal_transaction(start):
                solver = Solver()
                end.constrain(solver)
                assert solver.check()

                ok = validate(factory.address, address, end.universe)
                solver.assert_and_track(ok)
                if solver.check():
                    solution = end.transaction.calldata.evaluate(solver, True)
            print(solution if solution is not None else "no solution")
        except Exception as e:
            suffix = ""
            if str(e) != "":
                suffix = f": {e}"
            print(f"{e.__class__.__name__}{suffix}")
