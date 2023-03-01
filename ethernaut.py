#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
from collections import defaultdict
from time import sleep
from typing import Dict, List, Optional, Tuple

from environment import Contract, Universe
from rpc import get_code, get_storage_at
from smt import Uint160, Uint256
from solidity import abiencode
from state import State
from vm import (
    concrete_CREATE,
    concrete_GAS,
    concrete_JUMPI,
    concrete_start,
    hybrid_CALL,
    step,
)

CONTROLLER = Uint160(0xD2E5E0102E55A5234379DD796B8C641CD5996EFD)

LEVELS = [
    # 00 - Hello Ethernaut
    Uint160(0xBA97454449C10A0F04297022646E7750B8954EE8),
    # 01 - Fallback
    Uint160(0x80934BE6B8B872B364B470CA30EAAD8AEAC4F63F),
    # 02 - Fallout
    Uint160(0x0AA237C34532ED79676BCEA22111EA2D01C3D3E7),
]


def setup(address: Uint160) -> Tuple[Contract, Universe]:
    """Call createLevelInstance to set up the level."""
    calldata = abiencode("createLevelInstance(address)") + address.into(Uint256).unwrap(
        bytes
    )

    controller = get_code(CONTROLLER)
    contracts: Dict[int, Contract] = {}
    while True:
        start = concrete_start(copy.deepcopy(controller), Uint256(0), calldata)
        for contract in contracts.values():
            start.universe.add_contract(copy.deepcopy(contract))

        end, accessed = _execute(start)
        if end.success is True:
            break

        for addr, keys in accessed.items():
            if addr == 0x70D070D070D070D070D070D070D070D070D070D0:
                continue
            if addr == CONTROLLER.unwrap():
                contract = controller
            else:
                if addr not in contracts:
                    contracts[addr] = get_code(Uint160(addr))
                contract = contracts[addr]
            for key in keys:
                if key.unwrap() not in contract.storage.surface:
                    val = get_storage_at(Uint160(addr), key)
                    sleep(0.25)
                    contract.storage.poke(key, val)

    assert len(end.logs) == 1
    assert len(end.logs[0].topics) == 4
    address = end.logs[0].topics[2].into(Uint160)
    level = end.universe.contracts[address.unwrap()]

    assert id(end.contract) == id(end.universe.contracts[CONTROLLER.unwrap()])

    return level, end.universe


def check(level: Contract, universe: Universe) -> None:
    """Call submitLevelInstance to check the solution."""
    controller = universe.contracts[CONTROLLER.unwrap()]
    calldata = abiencode("submitLevelInstance(address)") + level.address.into(
        Uint256
    ).unwrap(bytes)

    start = concrete_start(controller, Uint256(0), calldata)
    start.universe = universe

    end, _ = _execute(start, 0)
    assert end.success is not None
    if end.success is False:
        raise RuntimeError(end.returndata.unwrap()[68:].strip(b"\x00").decode())


def _execute(
    state: State, indent: Optional[int] = None
) -> Tuple[State, Dict[int, List[Uint256]]]:
    accessed: Dict[int, List[Uint256]] = defaultdict(list)

    while True:
        instr = state.contract.program.instructions[state.pc]
        if indent is not None:
            print(" " * indent, instr)

        if instr.name == "EXTCODESIZE":
            address = state.stack[-1].into(Uint160)
            if address.unwrap() not in state.universe.contracts:
                accessed[address.unwrap()]
                return state, accessed

        action = step(state)
        if action == "CONTINUE":
            pass
        elif action == "JUMPI":
            concrete_JUMPI(state)
        elif action == "GAS":
            concrete_GAS(state)
        elif action == "CALL":
            address = state.stack[-2].into(Uint160)
            if address.unwrap() not in state.universe.contracts:
                accessed[address.unwrap()]
                return state, accessed
            for substate in hybrid_CALL(state):
                substate, subaccessed = _execute(
                    substate, indent + 2 if indent is not None else None
                )
                for s, v in subaccessed.items():
                    accessed[s].extend(v)
        elif action == "DELEGATECALL":
            # We can skip this opcode because it's only used to call the
            # statistics library.
            for _ in range(6):
                state.stack.pop()
            state.stack.append(Uint256(1))
        elif action == "CREATE":
            with concrete_CREATE(state) as substate:
                _, subaccessed = _execute(
                    substate, indent + 2 if indent is not None else None
                )
                for s, v in subaccessed.items():
                    accessed[s].extend(v)
        elif action == "TERMINATE":
            break
        else:
            raise NotImplementedError(action)

        if indent is not None:
            for y in reversed(state.stack):
                print("      ", y.describe())

    for contract in state.universe.contracts.values():
        accessed[contract.address.unwrap()].extend(contract.storage.accessed)
    accessed[state.contract.address.unwrap()].extend(state.contract.storage.accessed)
    return state, accessed


if __name__ == "__main__":
    for address in LEVELS:
        level, universe = setup(address)
        check(level, universe)
