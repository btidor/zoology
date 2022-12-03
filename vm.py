#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

import inspect
from typing import Iterator, List, Literal, Optional, assert_never

import z3

import ops
from disassembler import Instruction, Program, disassemble
from environment import Block, Contract, Universe
from sha3 import SHA3
from state import State
from symbolic import BA, BW, Array, Bytes, uint256, unwrap, unwrap_bytes


def step(state: State) -> Literal["CONTINUE", "JUMPI", "TERMINATE"]:
    """
    Execute a single instruction.

    Mutates state. The caller must handle the return value, which indicates
    whether the program (a) continues normally, or (b) hits a conditional jump
    (JUMPI), or (c) terminates

    In the case of a JUMPI, state is not modified. The caller must evaluate
    whether or not the jump should be taken, update the program counter, and
    optionally add symbolic constraints.
    """
    program = state.contract.program
    ins = program.instructions[state.pc]

    if ins.name == "JUMPI":
        return "JUMPI"
    elif hasattr(ops, ins.name):
        fn = getattr(ops, ins.name)
        sig = inspect.signature(fn)
        args: List[object] = []
        for name in sig.parameters:
            kls = sig.parameters[name].annotation
            if kls == uint256:
                args.append(state.stack.pop())
            elif kls == State:
                args.append(state)
            elif kls == Universe:
                args.append(state.universe)
            elif kls == Block:
                args.append(state.block)
            elif kls == Contract:
                args.append(state.contract)
            elif kls == Instruction:
                args.append(ins)
            elif kls == Program:
                args.append(program)
            else:
                raise TypeError(f"unknown arg class: {kls}")

        result: Optional[uint256] = fn(*args)
        if result is not None:
            state.stack.append(result)
            if len(state.stack) > 1024:
                raise Exception("evm stack overflow")

        state.pc += 1

        if state.success is None:
            return "CONTINUE"
        else:
            return "TERMINATE"
    else:
        raise ValueError(f"unimplemented opcode: {ins.name}")


def printable_execution(state: State) -> Iterator[str]:
    """
    Invoke a contract with concrete inputs and state.

    Yields a human-readable string at each step of the program.
    """
    program = state.contract.program
    while True:
        # Print next instruction
        ins = program.instructions[state.pc]
        yield str(ins)

        # Execute a single instruction with concrete jumps
        action = step(state)

        if action == "CONTINUE" or action == "TERMINATE":
            pass
        elif action == "JUMPI":
            concrete_JUMPI(state)
        else:
            assert_never(action)

        # Print stack
        for x in state.stack:
            yield "  " + unwrap_bytes(x).hex()
        yield ""

        if action == "TERMINATE":
            break

    yield ("RETURN" if state.success else "REVERT") + " " + str(
        state.returndata.require_concrete()
    )


def concrete_JUMPI(state: State) -> None:
    """Handle a JUMPI action with concrete arguments. Mutates state."""
    program = state.contract.program
    counter = unwrap(state.stack.pop(), "JUMPI(counter, b) requires concrete counter")
    b = unwrap(state.stack.pop(), "JUMPI(counter, b) requires concrete b")
    if counter not in program.jumps:
        raise ValueError(f"illegal JUMPI target: 0x{counter:x}")
    if b == 0:
        state.pc += 1
    else:
        state.pc = program.jumps[counter]


def concrete_start(program: Program) -> State:
    """Return a concrete start state with realistic values."""
    block = Block(
        number=BW(16030969),
        coinbase=BA(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5),
        timestamp=BW(1669214471),
        prevrandao=BW(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        ),
        gaslimit=BW(30000000000000000),
        chainid=BW(1),
        basefee=BW(12267131109),
    )
    contract = Contract(
        program=program,
        storage=Array("STORAGE", z3.BitVecSort(256), BW(0)),
    )
    universe = Universe(
        suffix="",
        balances=Array("BALANCE", z3.BitVecSort(160), BW(0)),
        transfer_constraints=[],
        agents=[],
        contribution=BW(0),
        extraction=BW(0),
    )
    return State(
        suffix="",
        block=block,
        contract=contract,
        universe=universe,
        sha3=SHA3(),
        pc=0,
        stack=[],
        memory={},
        address=BA(0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA),
        origin=BA(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB),
        caller=BA(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB),
        callvalue=BW(0),
        calldata=Bytes("CALLDATA", b"\x6f\xab\x5d\xdf"),
        gasprice=BW(0x12),
        returndata=Bytes("", b""),
        success=None,
        path_constraints=[],
        path=1,
    )


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)
    start = concrete_start(program)

    for line in printable_execution(start):
        print(line)
