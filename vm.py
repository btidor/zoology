#!/usr/bin/env python3

import inspect
from typing import Any, List, Optional, cast

import z3

import ops
from common import BW, Block, ByteArray, State, hexify, require_concrete, uint256
from disassembler import Instruction, Program, disassemble


def execute(
    program: Program,
    block: Block,
    s: State,
    output: bool = False,
) -> List[State]:
    jumps = None
    while True:
        ins = program.instructions[s.pc]
        s.pc += 1

        if output:
            print_instruction(ins)

        if ins.name == "JUMPI":
            jumps = handle_JUMPI(program, s)
        elif hasattr(ops, ins.name):
            fn = getattr(ops, ins.name)
            dispatch_opcode(program, block, s, ins, fn)
        else:
            raise ValueError(f"unimplemented opcode: {ins.name}")

        if output:
            print_stack(s.stack)
            print()

        if jumps:
            return jumps
        elif s.success is not None:
            return [s]


def handle_JUMPI(p: Program, s: State) -> List[State]:
    counter = require_concrete(
        s.stack.pop(), "JUMPI(counter, b) requires concrete counter"
    )
    if counter not in p.jumps:
        raise ValueError(f"illegal JUMPI target: 0x{counter:x}")
    b = cast(uint256, z3.simplify(s.stack.pop()))

    s2 = s.copy()
    s.constraints.append(b == BW(0))
    s.path = s.path << 1
    s2.constraints.append(b != BW(0))
    s2.path = (s.path << 1) | 1
    s2.pc = p.jumps[counter]
    return [s, s2]


def dispatch_opcode(
    program: Program, block: Block, s: State, ins: Instruction, fn: Any
) -> None:
    sig = inspect.signature(fn)
    args: List[object] = []
    for name in sig.parameters:
        kls = sig.parameters[name].annotation
        if kls == uint256:
            args.append(s.stack.pop())
        elif kls == State:
            args.append(s)
        elif kls == Block:
            args.append(block)
        elif kls == Instruction:
            args.append(ins)
        elif kls == Program:
            args.append(program)
        else:
            raise TypeError(f"unknown arg class: {kls}")

    result: Optional[uint256] = fn(*args)
    if result is not None:
        s.stack.append(result)
        if len(s.stack) > 1024:
            raise Exception("evm stack overflow")


def print_instruction(ins: Instruction) -> None:
    msg = f"{(ins.offset):04x}  {ins.name}"
    if ins.suffix is not None:
        msg += str(ins.suffix)
    if ins.operand is not None:
        msg += "\t" + hex(require_concrete(ins.operand))
    print(msg)


def print_stack(stack: List[uint256]) -> None:
    for x in stack:
        x = z3.simplify(x)
        if z3.is_bv_value(x):
            print(" ", hexify(x, 32))
        else:
            print(" ", x)


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)
    block = Block()
    state = State(
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", b"\x6f\xab\x5d\xdf"),
    )
    while state.success is None:
        states = execute(program, block, state, True)
        if len(states) < 2:
            continue

        a, b = states
        p = z3.simplify(z3.And(*a.constraints))
        q = z3.simplify(z3.And(*b.constraints))

        if p == True and q == False:
            state = a
        elif p == False and q == True:
            state = b
        else:
            raise ValueError("ambiguous JUMPI, did we accidentally symbolize?")

    result = bytes(
        require_concrete(d, "return data must be concrete") for d in state.returndata
    )
    print("RETURN" if state.success else "REVERT", result)
