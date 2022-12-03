#!/usr/bin/env python3
"""A universal transaction solver."""

from typing import Iterator, Tuple, assert_never

import z3

from _common import print_solution
from disassembler import Program, disassemble
from environment import Block, Contract, Universe
from sha3 import SHA3
from state import State
from symbolic import Array, Bytes, check, concretize
from vm import step


def universal_transaction(
    program: Program, sha3: SHA3, suffix: str = ""
) -> Iterator[Tuple[State, State]]:
    """
    Compute the "universal transaction" over a fully symbolic input.

    Execute the given program with a fully-symbolic start state. Yield every
    possible state pair `(start, end)`, where `start` is a constant and `end` is
    a state that RETURNs.

    If you're going to further constrain the end states using expressions from a
    prior execution of `universal_transaction()`, the two executions should have
    a different suffix.
    """
    start = symbolic_start(program, sha3, suffix)

    init = start.copy()
    init.universe.transfer(init.caller, init.address, init.callvalue)
    states = [init]

    while len(states) > 0:
        state = states.pop()

        while True:
            action = step(state)
            if action == "CONTINUE":
                continue
            elif action == "JUMPI":
                states.extend(symbolic_JUMPI(program, state))
                break
            elif action == "TERMINATE":
                assert state.success is not None
                if state.success:
                    yield start, state
                break
            else:
                assert_never(action)


def symbolic_JUMPI(program: Program, state: State) -> Iterator[State]:
    """Handle a JUMPI action with a symbolic condition. Yields next states."""
    solver = z3.Optimize()
    state.constrain(solver)

    counter = concretize(
        state.stack.pop(), "JUMPI(counter, b) requires concrete counter"
    )
    if counter not in program.jumps:
        raise ValueError(f"illegal JUMPI target: 0x{counter:x}")
    b = state.stack.pop()

    if check(solver, b == 0):
        next = state.copy()
        next.pc += 1
        next.path = (next.path << 1) | 0
        next.path_constraints.append(b == 0)
        yield next

    if check(solver, b != 0):
        next = state.copy()
        next.pc = program.jumps[counter]
        next.path = (next.path << 1) | 1
        next.path_constraints.append(b != 0)
        yield next


def symbolic_start(program: Program, sha3: SHA3, suffix: str) -> State:
    """Return a fully-symbolic start state."""
    block = Block(
        number=z3.BitVec(f"NUMBER{suffix}", 256),
        coinbase=z3.BitVec(f"COINBASE{suffix}", 160),
        timestamp=z3.BitVec(f"TIMESTAMP{suffix}", 256),
        prevrandao=z3.BitVec(f"PREVRANDAO{suffix}", 256),
        gaslimit=z3.BitVec(f"GASLIMIT{suffix}", 256),
        chainid=z3.BitVec(f"CHAINID", 256),
        basefee=z3.BitVec(f"BASEFEE{suffix}", 256),
    )
    contract = Contract(
        program=program,
        storage=Array(f"STORAGE{suffix}", z3.BitVecSort(256), z3.BitVecSort(256)),
    )
    caller = z3.BitVec(f"CALLER", 160)
    universe = Universe(
        suffix=suffix,
        # TODO: the balances of other accounts can change between transactions
        # (and the balance of this contract account too, via SELFDESTRUCT). How
        # do we model this?
        balances=Array(f"BALANCES{suffix}", z3.BitVecSort(160), z3.BitVecSort(256)),
        transfer_constraints=[],
        agents=[caller],
        contribution=z3.BitVec(f"CONTRIBUTION{suffix}", 256),
        extraction=z3.BitVec(f"EXTRACTION{suffix}", 256),
    )
    return State(
        suffix=suffix,
        block=block,
        contract=contract,
        universe=universe,
        sha3=sha3,
        pc=0,
        stack=[],
        memory={},
        address=z3.BitVec("ADDRESS", 160),
        # TODO: properly constrain ORIGIN to be an EOA and CALLER to either be
        # equal to ORIGIN or else be a non-EOA; handle the case where ORIGIN and
        # CALLER vary across transactions.
        origin=caller,
        caller=caller,
        callvalue=z3.BitVec(f"CALLVALUE{suffix}", 256),
        calldata=Bytes(f"CALLDATA{suffix}"),
        gasprice=z3.BitVec(f"GASPRICE{suffix}", 256),
        returndata=[],
        success=None,
        path_constraints=[],
        path=1,
    )


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)
    for start, end in universal_transaction(program, SHA3(), ""):
        print_solution(start, end)

    print("End Universal Transaction")
