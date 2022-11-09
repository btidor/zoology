#!/usr/bin/env python3
from typing import Dict, List

from common import OPCODES, Instruction, Program


def parse_program(code: bytes) -> Program:
    # Iterate over instructions
    idx = 0
    instructions: List[Instruction] = []
    jumps: Dict[int, int] = {}
    while idx < len(code):
        op = OPCODES.get(code[idx])
        idx += 1
        data = None

        if op is None:
            instructions.append(Instruction(None, None))
        elif op.name == "JUMPDEST":
            jumps[idx - 1] = len(instructions)
            # omit the JUMPDEST instruction from the emitted program
            # TODO: make sure we properly handle a program ending in JUMPDEST
        elif op.name == "PUSH":
            # PUSH is the only opcode that takes an operand...?
            n = int(op.fullName[4:])
            data = code[idx : idx + n]
            idx += n
            instructions.append(Instruction(op, data))
        else:
            instructions.append(Instruction(op, None))

    return Program(instructions, jumps)


def disassemble(code: bytes) -> None:
    # Strip the optional contract metadata trailer:
    # https://docs.soliditylang.org/en/latest/metadata.html#encoding-of-the-metadata-hash-in-the-bytecode
    trailer = code[-54:]
    if (
        trailer.startswith(b"\xfe\xa2\x64ipfs\x58\x22")
        and trailer.endswith(b"\x00\x33")
        and len(trailer) == 54
    ):
        code = code[:-53]  # preserve the INVALID spacer
    else:
        trailer = b""

    program = parse_program(code)
    print(program)
    for instr in program.instructions:
        op = instr.opcode
        if op:
            print(
                f"{op.fullName.ljust(12)} ({op.fee: 5}{'*' if op.dynamicGas else ' '})",
                end="",
            )
        else:
            print("???", end="")
        if instr.operand:
            text = None
            if len(instr.operand) > 3:
                try:
                    text = instr.operand.decode("ascii")
                except UnicodeDecodeError:
                    pass
            print(f"  {'0x' + instr.operand.hex()} {text or ''}", end="")
        print()

    if trailer:
        print(f"> ignoring metadata trailer{' (**)' if 0x5B in trailer else ''} <")


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    disassemble(code)
