#!/usr/bin/env pytest

import pytest
import z3

from disassembler import disassemble
from sha3 import SHA3
from symbolic import check, solver_stack
from universal import constrain_to_goal, printable_transition, universal_transaction


def test_basic() -> None:
    code = bytes.fromhex("60FF60EE5560AA60AA03600E57005B60006000FD")
    program = disassemble(code)
    sha3 = SHA3()

    universal = universal_transaction(program, sha3, "")

    start, end = next(universal)
    assert end.success == True

    solver = z3.Optimize()
    end.constrain(solver)
    with solver_stack(solver):
        constrain_to_goal(solver, start, end)
        assert not check(solver)
    assert check(solver)

    raw = """
        ---  📒 STEP\tRETURN\tPx2\t---------------------------------------------------------

        Caller\t0xcacacacacacacacacacacacacacacacacacacaca

        Address\t0xadadadadadadadadadadadadadadadadadadadad

        Balance\tR: 0xadadadadadadadadadadadadadadadadadadadad
        \t-> 0x8000000000001
        \tR: 0xcacacacacacacacacacacacacacacacacacacaca
        \t-> 0x0
        \tW: 0xadadadadadadadadadadadadadadadadadadadad
        \t-> 0x8000000000001 (no change)
        \tW: 0xcacacacacacacacacacacacacacacacacacacaca
        \t-> 0x0 (no change)

        Storage\tW: 0xee -> 0xff (from 0x0)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:])

    for actual, expected in zip(printable_transition(start, end), fixture, strict=True):
        assert actual.strip(" ") == expected

    with pytest.raises(StopIteration):
        next(universal)
