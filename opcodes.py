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


# We autogenerate the list of opcodes from the @ethereumjs node package. To
# re-generate, run:
#
# $ npm install @ethereumjs/common@latest
# $ npm install @ethereumjs/evm@latest
# $ ./fetchOpcodes.js > opcodes.json
#
def _load_opcodes() -> Dict[int, Opcode]:
    with open("opcodes.json") as f:
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
