import json
from dataclasses import dataclass
from typing import Dict


@dataclass
class Opcode:
    code: int
    name: str
    fullName: str
    fee: int
    isAsync: bool
    dynamicGas: bool


def _load_opcodes() -> Dict[int, Opcode]:
    with open("opcodes.json") as f:
        raw = json.load(f)
        tuples = [Opcode(**item) for item in raw]
        return dict((item.code, item) for item in tuples)


REFERENCE = _load_opcodes()
