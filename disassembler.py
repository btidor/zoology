"""An EVM bytecode disassembler."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

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
            instruction = decode_instruction(data, offset)
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


def decode_instruction(code: bytes | Bytes, offset: int) -> Instruction:
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
