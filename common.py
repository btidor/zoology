from dataclasses import dataclass, field
from typing import Dict, Optional

uint256 = int
Address = int


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
    jumps: Dict[uint256, int] = field(default_factory=dict)
    memory: Dict[uint256, int] = field(default_factory=dict)  # index -> 1-byte value
    address: Address = 0
    origin: Address = 0
    caller: Address = 0
    callvalue: uint256 = 0
    calldata: bytes = b""
    gasprice: uint256 = 0
    returndata: bytes = b""
    success: Optional[bool] = None
    storage: Dict[uint256, uint256] = field(default_factory=dict)
