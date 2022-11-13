from dataclasses import dataclass, field
from typing import Dict, Optional, TypeAlias

import z3

uint8: TypeAlias = z3.BitVecRef
uint256: TypeAlias = z3.BitVecRef
Address: TypeAlias = z3.BitVecRef


def BW(i: int) -> uint256:
    if i >= (1 << 256) or i < 0:
        raise ValueError(f"invalid word: {i}")
    return z3.BitVecVal(i, 256)


def BY(i: int) -> uint8:
    if i >= (1 << 8) or i < 0:
        raise ValueError(f"invalid byte: {i}")
    return z3.BitVecVal(i, 8)


@dataclass
class Opcode:
    code: int
    name: str
    fullName: str
    fee: int
    isAsync: bool
    dynamicGas: bool


@dataclass
class Instruction:
    name: str
    suffix: Optional[int] = None
    operand: Optional[uint256] = None


@dataclass
class State:
    pc: int = 0
    jumps: Dict[int, int] = field(default_factory=dict)
    memory: Dict[int, uint8] = field(
        default_factory=dict
    )  # concrete index -> 1-byte value
    address: Address = BW(0)
    origin: Address = BW(0)
    caller: Address = BW(0)
    callvalue: uint256 = BW(0)
    calldata: bytes = b""
    gasprice: uint256 = BW(0)
    returndata: bytes = b""
    success: Optional[bool] = None
    storage: Dict[int, uint256] = field(default_factory=dict)
