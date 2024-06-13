#!/usr/bin/env python3
"""An EVM bytecode disassembler."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable

from Crypto.Hash import keccak

from bytes import Bytes
from opcodes import REFERENCE, UNIMPLEMENTED
from smt import Uint, Uint256


@dataclass(frozen=True)
class Program:
    """The disassembled code of an EVM contract."""

    code: Bytes
    instructions: tuple[Instruction, ...]

    # Maps byte offsets in the contract, as used by JUMP/JUMPI, to an index into
    # `instructions`.
    jumps: dict[int, int]

    def __copy__(self) -> Program:
        return self

    def __deepcopy__(self, memo: Any) -> Program:
        return self


@dataclass(frozen=True)
class Instruction:
    """A single disassembled EVM instruction."""

    # Starting index of the instruction in the code, in bytes
    offset: int

    # Size of the instruction in the code, in bytes
    size: int

    # Simplified instruction name, e.g. DUP1 -> DUP
    name: str

    # Numeric suffix, e.g. 1 for DUP1
    suffix: int | None = None

    # Operand (PUSH and CUSTOM only)
    operand: Uint256 | CustomCopy | None = None

    def __str__(self) -> str:
        msg = f"{self.offset:04x}  {self.name}"
        if self.suffix is not None:
            msg += str(self.suffix)
        if isinstance(self.operand, Uint) and self.suffix is not None:
            assert (operand := self.operand.reveal()) is not None
            msg += "\t0x" + operand.to_bytes(self.suffix).hex()
        return msg


@dataclass
class CustomCopy:
    """An custom instruction to copy data between memory addresses."""

    start: Uint256
    end: Uint256
    stride: Uint256

    read: Uint256
    write: Uint256

    exit: int


class DisassemblyError(Exception):
    """Disassembly failed because the code was malformed."""

    pass


def abiencode(signature: str) -> bytes:
    """Encode a Solidity function-call signature."""
    return keccak.new(data=signature.encode(), digest_bits=256).digest()[:4]


def disassemble(code: Bytes) -> Program:
    """Parse and validate an EVM contract's code."""
    instructions = list[Instruction]()
    jumps = dict[int, int]()
    offset = 0
    trailer = None
    data = code.reveal() or code
    n = code.length.reveal()
    assert n is not None, "disassemble requires concrete-length code"

    while offset < n:
        try:
            instruction = _decode_instruction(data, offset)
        except DisassemblyError:
            if trailer is None:
                raise
            instructions = instructions[:trailer]
            break

        instructions.append(instruction)
        if instruction.name == "JUMPDEST":
            jumps[offset] = len(instructions) - 1

        offset += instruction.size

        # The Solidity compiler emits the opcode INVALID (0xFE) to separate the
        # program from non-code trailers, like strings and contract metadata.
        # However, INVALID is also emitted as part of some assertion checks.
        #
        # https://docs.soliditylang.org/en/latest/metadata.html
        #
        # If we encounter INVALID, try to decode the following bytes. If they're
        # not valid code, discard them and end dissasembly.
        #
        if instruction.name == "INVALID":
            trailer = len(instructions)

    return Program(
        code=code,
        instructions=tuple(instructions),
        jumps=jumps,
    )


def _decode_instruction(code: bytes | Bytes, offset: int) -> Instruction:
    """Decode a single instruction from the given offset within `code`."""
    if isinstance(code, bytes):
        opcode = code[offset]
    else:
        opcode = code[Uint256(offset)].reveal()
        if opcode is None:
            raise DisassemblyError(f"unexpected symbolic opcode at offset {offset}")

    opref = REFERENCE.get(opcode)
    if opref is None:
        raise DisassemblyError(f"unknown opcode: 0x{opcode:02x}")
    size = 1
    suffix = None
    operand = None

    name = opref.name
    if name == "PUSH" or name == "PUSH0":
        name = "PUSH"
        # PUSH is the only opcode that takes an operand
        suffix = opref.code - 0x5F
        if isinstance(code, bytes):
            buf = 0
            for i in range(suffix):
                buf = (buf << 8) | code[offset + i + 1]
            operand = Uint256(buf)
        else:
            operand = Uint256(0)
            for i in range(suffix):
                byte = code[Uint256(offset + i + 1)].into(Uint256)
                operand = (operand << Uint256(8)) | byte
        size = suffix + 1
    elif name == "DUP":
        suffix = opref.code - 0x7F
    elif name == "SWAP":
        suffix = opref.code - 0x8F
    elif name == "LOG":
        suffix = opref.code - 0xA0
    elif name in UNIMPLEMENTED:
        raise ValueError(f"unimplemented opcode: {opref.fullName}")

    return Instruction(offset, size, name, suffix, operand)


def printable_disassembly(code: Bytes) -> Iterable[str]:
    """Produce a human-readable transcript of disassembly."""
    assert (data := code.reveal()) is not None
    offset = 0
    while offset < len(data):
        ins = _decode_instruction(data, offset)
        assert ins is not None
        yield str(ins)

        offset += ins.size

        if ins.name == "INVALID":
            break


if __name__ == "__main__":
    code = Bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    for line in printable_disassembly(code):
        print(line)
