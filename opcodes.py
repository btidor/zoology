import json
from typing import Dict

from common import Opcode


def _load_opcodes() -> Dict[int, Opcode]:
    with open("opcodes.json") as f:
        raw = json.load(f)
        tuples = [Opcode(**item) for item in raw]
        return dict((item.code, item) for item in tuples)


REFERENCE = _load_opcodes()
