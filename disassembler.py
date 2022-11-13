#!/usr/bin/env python3

from typing import Dict, List, Tuple

import ops
from common import BW, Instruction
from opcodes import REFERENCE


def disassemble(code: bytes) -> Tuple[List[Instruction], Dict[int, int]]:
    idx = 0
    parsed: List[Instruction] = []
    jumps: Dict[int, int] = {}
    while idx < len(code):
        opcode = code[idx]
        idx += 1

        opref = REFERENCE.get(opcode)
        if opref is None:
            raise ValueError(f"unknown opcode: 0x{opcode:02x}")
        elif opref.name == "PUSH":
            # PUSH is the only opcode that takes an operand.
            n = opref.code - 0x5F
            operand = 0
            for i in range(n):
                operand = (operand << 8) | code[idx]
                idx += 1
            parsed.append(Instruction(opref.name, operand=BW(operand)))
        elif opref.name == "DUP":
            n = opref.code - 0x7F
            parsed.append(Instruction(opref.name, suffix=n))
        elif opref.name == "SWAP":
            n = opref.code - 0x8F
            parsed.append(Instruction(opref.name, suffix=n))
        elif opref.name == "PC":
            # 58 - Get the value of the program counter prior to the increment
            # corresponding to this instruction
            parsed.append(Instruction(opref.name, operand=BW(idx - 1)))
        elif opref.name == "JUMPDEST":
            # 5B - Marks a valid destination for jumps
            #
            # Since this opcode is a no-op, we strip it out of the instruction
            # stream.
            jumps[idx - 1] = len(parsed)
        elif opref.name == "INVALID":
            # If we encounter the reserved opcode INVALID (0xFE), assume the
            # remaining data is a non-code trailer, e.g. contract metadata.
            parsed.append(Instruction(opref.name))
            break
        elif hasattr(ops, opref.fullName):
            parsed.append(Instruction(opref.name))
        else:
            # TODO: raise ValueError(f"unimplemented opcode: {opref.fullName}")
            parsed.append(Instruction(opref.name))

    # Insert a synthetic STOP instruction in case we fall through the end of the
    # code. This results in the correct (??) behavior.
    parsed.append(Instruction("STOP"))

    return (parsed, jumps)


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, _ = disassemble(code)
    for i, ins in enumerate(instructions[:-1]):  # skip trailing STOP
        msg = f"{i: 4}\t{ins.name}"
        if ins.suffix is not None:
            msg += str(ins.suffix)
        if ins.operand is not None:
            msg += "\t" + hex(ins.operand.as_long())
        print(msg)
