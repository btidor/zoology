#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
from collections import defaultdict
from typing import Dict, List, Tuple, cast

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
    contracts = {CONTROLLER.unwrap(): controller}
    while True:
        start = concrete_start(controller.program, Uint256(0), calldata)
        start.contract = copy.deepcopy(controller)
        for contract in contracts.values():
            start.universe.add_contract(copy.deepcopy(contract))

        end, accessed = _execute(start)
        if end.success is True:
            break

        for addr, keys in accessed.items():
            if addr == 0x70D070D070D070D070D070D070D070D070D070D0:
                continue
            if addr not in contracts:
                contracts[addr] = get_code(Uint160(addr))
            for key in keys:
                if key.unwrap() not in contracts[addr].storage.surface:
                    val = get_storage_at(Uint160(addr), key)
                    contracts[addr].storage.poke(key, val)

    level = end.universe.contracts[int.from_bytes(end.returndata.unwrap())]
    return level, end.universe


def check(level: Contract, universe: Universe) -> None:
    """Call submitLevelInstance to check the solution."""
    controller = universe.contracts[CONTROLLER.unwrap()]
    calldata = abiencode("submitLevelInstance(address)") + level.address.into(
        Uint256
    ).unwrap(bytes)

    start = concrete_start(controller.program, Uint256(0), calldata)
    start.universe = copy.deepcopy(universe)

    end, _ = _execute(start)
    assert end.success is not None
    if end.success is False:
        raise RuntimeError(end.returndata.unwrap()[68:].strip(b"\x00").decode())


def _execute(state: State, indent: int = 0) -> Tuple[State, Dict[int, List[Uint256]]]:
    accessed: Dict[int, List[Uint256]] = defaultdict(list)

    while True:
        instr = state.contract.program.instructions[state.pc]
        # print(" " * indent, instr)

        if instr.name == "EXTCODESIZE":
            address = state.stack[-1].into(Uint160)
            if address.unwrap() not in state.universe.contracts:
                accessed[address.unwrap()]
                return state, accessed
        elif instr.name == "LOG":
            state.pc += 1
            for _ in range(2 + cast(int, instr.suffix)):
                state.stack.pop()
            continue

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
                substate, subaccessed = _execute(substate, indent + 2)
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
                _, subaccessed = _execute(substate, indent + 2)
                for s, v in subaccessed.items():
                    accessed[s].extend(v)
        elif action == "TERMINATE":
            break
        else:
            raise NotImplementedError(action)

        # for y in reversed(state.stack):
        #     print("      ", y.describe())

    for contract in state.universe.contracts.values():
        accessed[contract.address.unwrap()].extend(contract.storage.accessed)
    accessed[state.contract.address.unwrap()].extend(state.contract.storage.accessed)
    return state, accessed


if __name__ == "__main__":
    for address in LEVELS:
        level, universe = setup(address)
        check(level, universe)
