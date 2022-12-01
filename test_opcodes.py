#!/usr/bin/env pytest

import _ops
from _opcodes import REFERENCE, UNIMPLEMENTED


def test_all_opcodes_implemented() -> None:
    for opcode in REFERENCE.values():
        if opcode.name in UNIMPLEMENTED:
            continue
        assert hasattr(
            _ops, opcode.fullName
        ), f"unimplemented opcode: {opcode.fullName}"
