"""A library of EVM opcodes."""

import json
import os
from dataclasses import dataclass
from typing import Dict


@dataclass
class Opcode:
    """An EVM operation."""

    code: int
    name: str
    fullName: str
    fee: int
    isAsync: bool
    dynamicGas: bool


# We autogenerate the list of opcodes from the @ethereumjs node package. To
# re-generate, run:
#
# $ npm install @ethereumjs/common@latest
# $ npm install @ethereumjs/evm@latest
# $ ./fetchOpcodes.js > opcodes.json
#
_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), "opcodes.json")


def _load_opcodes() -> Dict[int, Opcode]:
    with open(_PATH) as f:
        raw = json.load(f)
        tuples = [Opcode(**item) for item in raw]
        return dict((item.code, item) for item in tuples)


REFERENCE = _load_opcodes()

UNIMPLEMENTED = set(
    [
        # Handled specially
        "PUSH",
        "DUP",
        "SWAP",
        # Removed in Merge fork
        "DIFFICULTY",
    ]
)
