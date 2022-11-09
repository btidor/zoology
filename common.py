import json
from dataclasses import dataclass
from typing import Dict, List, Optional


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
    opcode: Optional[Opcode]  # else invalid
    operand: Optional[bytes]


@dataclass
class Program:
    instructions: List[Instruction]
    jumps: Dict[int, int]  # raw offset -> pc


@dataclass
class Context:
    caller: int
    calldata: bytes
    value: int
    pc: Optional[int]  # index into instructions, None means halt
    stack: List[int]  # bottom...top ; TODO: max 1024 elements
    memory: Dict[int, int]
    storage: Dict[int, int]
    exit: Optional[str]


def _load_opcodes() -> Dict[int, Opcode]:
    with open("opcodes.json") as f:
        raw = json.load(f)
        tuples = [Opcode(**item) for item in raw]
        return dict((item.code, item) for item in tuples)


OPCODES = _load_opcodes()
