#!/usr/bin/env python3
"""An EVM bytecode disassembler."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, cast

from _opcodes import REFERENCE, UNIMPLEMENTED
from _symbolic import BW, require_concrete, uint256


@dataclass
class Program:
    """The disassembled code of an EVM contract."""

    instructions: List[Instruction] = field(default_factory=list)

    # Maps byte offsets in the contract, as used by JUMP/JUMPI, to an index into
    # `instructions`.
    jumps: Dict[int, int] = field(default_factory=dict)


@dataclass
class Instruction:
    """A single disassembled EVM instruction."""

    # Starting index of the instruction in the code, in bytes
    offset: int

    # Size of the instruction in the code, in bytes
    size: int

    # Simplified instruction name, e.g. DUP1 -> DUP
    name: str

    # Numeric suffix, e.g. 1 for DUP1
    suffix: Optional[int] = None

    # Operand (PUSH only)
    operand: Optional[uint256] = None

    def __str__(self) -> str:
        msg = f"{self.offset:04x}  {self.name}"
        if self.suffix is not None:
            msg += str(self.suffix)
        if self.operand is not None:
            operand = require_concrete(self.operand).to_bytes(
                cast(int, self.suffix), "big"
            )
            msg += "\t0x" + operand.hex()
        return msg


def disassemble(code: bytes) -> Program:
    """Parse and validate an EVM contract's code."""
    program = Program()

    offset = 0
    while offset < len(code):
        instruction = _decode_instruction(code, offset)

        program.instructions.append(instruction)
        if instruction.name == "JUMPDEST":
            program.jumps[offset] = len(program.instructions) - 1

        offset += instruction.size

        # If we encounter the reserved opcode INVALID (0xFE), assume the
        # remaining data is a non-code trailer, e.g. contract metadata.
        if instruction.name == "INVALID":
            break

    return program


def printable_disassembly(code: bytes) -> Iterable[str]:
    """
    Parse and validate an EVM contract's code.

    Yields a human-readable string for each instruction.
    """
    offset = 0
    while offset < len(code):
        ins = _decode_instruction(code, offset)
        yield str(ins)

        offset += ins.size

        if ins.name == "INVALID":
            break


def _decode_instruction(code: bytes, offset: int) -> Instruction:
    """Decode a single instruction from the given offset within `code`."""
    opcode = code[offset]
    opref = REFERENCE.get(opcode)
    size = 1
    suffix = None
    operand = None

    if opref is None:
        raise ValueError(f"unknown opcode: 0x{opcode:02x}")
    elif opref.name == "PUSH":
        # PUSH is the only opcode that takes an operand
        suffix = opref.code - 0x5F
        operand = 0
        for i in range(suffix):
            operand = (operand << 8) | code[offset + i + 1]
        operand = BW(operand)
        size = suffix + 1
    elif opref.name == "DUP":
        suffix = opref.code - 0x7F
    elif opref.name == "SWAP":
        suffix = opref.code - 0x8F
    elif opref.name in UNIMPLEMENTED:
        raise ValueError(f"unimplemented opcode: {opref.fullName}")

    return Instruction(offset, size, opref.name, suffix, operand)


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    for line in printable_disassembly(code):
        print(line)
