#!/usr/bin/env pytest

import z3

from common import BW, Block, ByteArray, State
from disassembler import disassemble
from vm import execute


def test_execute_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)

    block = Block()
    start = State(
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", b""),
    )

    fork = execute(program, block, start)
    assert len(fork) == 2

    assert fork[0].success is None
    assert fork[0].pc == 5
    assert z3.simplify(z3.And(*fork[0].constraints)) == False

    assert fork[1].success is None
    assert fork[1].pc == 6
    assert z3.simplify(z3.And(*fork[1].constraints)) == True

    branch = execute(program, block, fork[0])
    assert len(branch) == 1
    assert branch[0].success == True
    assert z3.simplify(z3.And(*branch[0].constraints)) == False

    branch = execute(program, block, fork[1])
    assert len(branch) == 1
    assert branch[0].success == False
    assert z3.simplify(z3.And(*branch[0].constraints)) == True
