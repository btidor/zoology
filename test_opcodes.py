#!/usr/bin/env pytest

import ops
from opcodes import REFERENCE, UNIMPLEMENTED


def test_all_opcodes_implemented() -> None:
    for opcode in REFERENCE.values():
        if opcode.name in UNIMPLEMENTED:
            continue
        assert hasattr(ops, opcode.fullName), f"unimplemented opcode: {opcode.fullName}"
