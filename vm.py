#!/usr/bin/env python3

import disassembler
from common import Context, Instruction, Program

MAX = 2**256


def execute(program: Program, calldata: bytes) -> None:
    ctx = Context(0xABCD, calldata, 0, 0, [], {}, {}, None)
    while ctx.pc is not None:
        instr = program.instructions[ctx.pc]
        dispatch(program, instr, ctx)
    print(f"Exit: {ctx.exit}")


def dispatch(program: Program, instr: Instruction, ctx: Context) -> None:
    if ctx.pc is not None:
        ctx.pc += 1

    print(
        instr.opcode.name if instr.opcode else "",
        instr.operand.hex() if instr.operand else "",
    )

    if instr.opcode is None:
        ctx.pc = None
        ctx.exit = "invalid instruction"
    elif instr.opcode.name == "STOP":
        ctx.pc = None
    elif instr.opcode.name == "ADD":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append((a + b) % MAX)
    elif instr.opcode.name == "MUL":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append((a * b) % MAX)
    elif instr.opcode.name == "SUB":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append((a - b) % MAX)
    elif instr.opcode.name == "DIV":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(a // b if b != 0 else 0)
    elif instr.opcode.name == "MOD":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(a % b if b != 0 else 0)
    elif instr.opcode.name == "LT":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(1 if a < b else 0)
    elif instr.opcode.name == "GT":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(1 if a > b else 0)
    elif instr.opcode.name == "EQ":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(1 if a == b else 0)
    elif instr.opcode.name == "ISZERO":
        a = ctx.stack.pop()
        ctx.stack.append(1 if a == 0 else 0)
    elif instr.opcode.name == "AND":
        a = ctx.stack.pop()
        b = ctx.stack.pop()
        ctx.stack.append(a & b)
    elif instr.opcode.name == "SHL":
        shift = ctx.stack.pop()
        value = ctx.stack.pop()
        ctx.stack.append((value << shift) % MAX)
    elif instr.opcode.name == "SHR":
        shift = ctx.stack.pop()
        value = ctx.stack.pop()
        ctx.stack.append(value >> shift)
    elif instr.opcode.name == "CALLER":
        ctx.stack.append(ctx.caller)
    elif instr.opcode.name == "CALLVALUE":
        ctx.stack.append(ctx.value)
    elif instr.opcode.name == "CALLDATALOAD":
        i = ctx.stack.pop()
        range = ctx.calldata[i : i + 32]
        range += b"\x00" * (32 - len(range))
        val = int.from_bytes(range, byteorder="big")
        ctx.stack.append(val)
    elif instr.opcode.name == "CALLDATASIZE":
        ctx.stack.append(len(ctx.calldata))
    elif instr.opcode.name == "JUMP":
        counter = ctx.stack.pop()
        ctx.pc = program.jumps[counter]  # TODO: handle error
    elif instr.opcode.name == "JUMPI":
        counter = ctx.stack.pop()
        b = ctx.stack.pop()
        if b != 0:
            print("***")
            ctx.pc = program.jumps[counter]  # TODO: handle error
    elif instr.opcode.name == "SELFBALANCE":
        ctx.stack.append(0)  # TODO
    elif instr.opcode.name == "POP":
        ctx.stack.pop()
    elif instr.opcode.name == "MLOAD":
        offset = ctx.stack.pop()
        ctx.stack.append(ctx.memory.get(offset, 0))
    elif instr.opcode.name == "MSTORE":
        offset = ctx.stack.pop()
        value = ctx.stack.pop()
        # TODO: handle IndexError (pop from empty list) correctly
        ctx.memory[offset] = value
    elif instr.opcode.name == "SLOAD":
        key = ctx.stack.pop()
        ctx.stack.append(ctx.storage.get(key, 0))
    elif instr.opcode.name == "PUSH":
        if instr.operand is None:
            raise ValueError("PUSH must have an operand")
        ctx.stack.append(int.from_bytes(instr.operand, byteorder="big"))
    elif instr.opcode.name == "DUP":
        n = int(instr.opcode.fullName[3:])
        val = ctx.stack[-n]
        ctx.stack.append(val)
    elif instr.opcode.name == "SWAP":
        n = int(instr.opcode.fullName[4:])
        ctx.stack[-1], ctx.stack[-n] = ctx.stack[-n], ctx.stack[-1]
    elif instr.opcode.name == "REVERT":
        ctx.pc = None
        ctx.exit = "REVERT"
    else:
        raise ValueError(f"unknown instruction {instr.opcode.name}")

    for x in ctx.stack:
        print(" ", int.to_bytes(x, 32, "big").hex())
    print()


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassembler.parse_program(code)
    execute(program, bytes.fromhex("8aa96f38"))
