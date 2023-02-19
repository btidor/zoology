#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
from collections import defaultdict
from typing import Dict, List, Tuple

from rpc import get_code, get_storage_at
from smt import Uint160, Uint256
from solidity import abiencode
from state import State
from vm import concrete_GAS, concrete_JUMPI, concrete_start, hybrid_CALL, step

PROGRAM = Uint160(0xD2E5E0102E55A5234379DD796B8C641CD5996EFD)

LEVELS = [
    # 00 - Hello Ethernaut
    Uint160(0xBA97454449C10A0F04297022646E7750B8954EE8),
    # 01 - Fallback
    Uint160(0x80934BE6B8B872B364B470CA30EAAD8AEAC4F63F),
    # 02 - Fallout
    Uint160(0x0AA237C34532ED79676BCEA22111EA2D01C3D3E7),
]


def play(address: Uint160) -> None:
    """Solve a given Ethernaut level."""
    calldata = abiencode("createLevelInstance(address)") + address.into(Uint256).unwrap(
        bytes
    )

    entrypoint = get_code(PROGRAM)
    contracts = {PROGRAM.unwrap(): entrypoint}
    while True:
        start = concrete_start(entrypoint.program, Uint256(0), calldata)
        start.contract = copy.deepcopy(entrypoint)
        for contract in contracts.values():
            start.universe.add_contract(copy.deepcopy(contract))

        end, accessed = _execute(start)
        assert end.success is False
        print(accessed)

        for addr, keys in accessed.items():
            if addr not in contracts:
                contracts[addr] = get_code(Uint160(addr))
            for key in keys:
                if key.unwrap() not in contracts[addr].storage.surface:
                    val = get_storage_at(Uint160(addr), key)
                    contracts[addr].storage.poke(key, val)

    raise NotImplementedError


def _execute(state: State) -> Tuple[State, Dict[int, List[Uint256]]]:
    accessed: Dict[int, List[Uint256]] = defaultdict(list)

    while True:
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
                state, subaccessed = _execute(substate)
                for k, v in subaccessed.items():
                    accessed[k].extend(v)
                break
        elif action == "TERMINATE":
            break
        else:
            raise NotImplementedError(action)

    for contract in state.universe.contracts.values():
        accessed[contract.address.unwrap()].extend(contract.storage.accessed)
    accessed[state.contract.address.unwrap()].extend(state.contract.storage.accessed)
    return state, accessed


if __name__ == "__main__":
    for level in LEVELS:
        play(level)
