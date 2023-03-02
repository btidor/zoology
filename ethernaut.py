#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

import copy
from collections import defaultdict
from time import sleep
from typing import Dict, List, Optional, Tuple

from environment import Contract, Universe
from rpc import get_code, get_storage_at
from sha3 import SHA3
from smt import Constraint, Uint160, Uint256
from solidity import abiencode
from solver import Solver
from state import State, Termination
from universal import _universal_transaction, printable_transition, symbolic_start
from vm import concrete_start, step

LEVEL_FACTORIES = [
    Uint160(0x2A2497AE349BCA901FEA458370BD7DDA594D1D69),
]


def create(factory: Contract) -> Tuple[Uint160, Universe]:
    """Call createInstance to set up the level."""
    caller = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    calldata = abiencode("createInstance(address)") + caller.into(Uint256).unwrap(bytes)
    contracts: Dict[int, Contract] = {}

    while True:
        start = concrete_start(copy.deepcopy(factory), Uint256(0), calldata)
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
    caller = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    calldata = (
        abiencode("validateInstance(address,address)")
        + instance.into(Uint256).unwrap(bytes)
        + caller.into(Uint256).unwrap(bytes)
    )

    universe = copy.deepcopy(universe)
    contract = universe.contracts[factory.unwrap()]
    start = concrete_start(contract, Uint256(0), calldata)
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

        if instr.name == "EXTCODESIZE":
            address = state.stack[-1].into(Uint160)
            if address.unwrap() not in state.universe.contracts:
                accessed[address.unwrap()]
                return state, accessed

        action = step(state)
        raise NotImplementedError("TODO")
        # if action == "CONTINUE":
        #     pass
        # elif action == "CALL":
        #     address = state.stack[-2].into(Uint160)
        #     if address.unwrap() not in state.universe.contracts:
        #         accessed[address.unwrap()]
        #         return state, accessed
        #     for substate in hybrid_CALL(state):
        #         substate, subaccessed = _execute(
        #             substate, indent + 2 if indent is not None else None
        #         )
        #         for s, v in subaccessed.items():
        #             accessed[s].extend(v)
        # elif action == "DELEGATECALL":
        #     # We can skip this opcode because it's only used to call the
        #     # statistics library.
        #     for _ in range(6):
        #         state.stack.pop()
        #     state.stack.append(Uint256(1))
        # elif action == "STATICCALL":
        #     with concrete_STATICCALL(state) as substate:
        #         substate, subaccessed = _execute(
        #             substate, indent + 2 if indent is not None else None
        #         )
        #         for s, v in subaccessed.items():
        #             accessed[s].extend(v)
        # elif action == "TERMINATE":
        #     break
        # else:
        #     raise NotImplementedError(action)

        if indent is not None:
            for y in reversed(state.stack):
                print("." * indent, " ", y.describe())

    for contract in state.universe.contracts.values():
        accessed[contract.address.unwrap()].extend(contract.storage.accessed)
    accessed[state.contract.address.unwrap()].extend(state.contract.storage.accessed)
    return state, accessed


if __name__ == "__main__":
    for address in LEVEL_FACTORIES:
        factory = get_code(address)
        address, universe = create(factory)

        instance = universe.contracts[address.unwrap()]
        start = symbolic_start(instance, SHA3(), "")
        start.universe = universe
        start.universe.transfer(
            start.transaction.caller,
            start.contract.address,
            start.transaction.callvalue,
        )

        solver = Solver()
        for end in _universal_transaction(start):
            end.universe.add_contract(end.contract)
            ok = validate(factory.address, address, end.universe)
            if solver.check(ok):
                for line in printable_transition(start, end):
                    print(line)
                break
