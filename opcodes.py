"""A library of EVM opcodes."""

import json
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
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

_FILENAME = Path(__file__).resolve().parent / "opcodes.json"


def _load_opcodes() -> dict[int, Opcode]:
    with open(_FILENAME) as f:
        raw = json.load(f)
        tuples = [Opcode(**item) for item in raw]
        return dict((item.code, item) for item in tuples)


REFERENCE = _load_opcodes()

SPECIAL = set(["PUSH", "DUP", "SWAP", "LOG", "CUSTOM"])

UNIMPLEMENTED = set(["PUSH0"])  # handled as PUSH<operand>
