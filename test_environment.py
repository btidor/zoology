#!/usr/bin/env pytest

import copy

import z3

from disassembler import disassemble
from sha3 import SHA3
from symbolic import BA, BW, Solver, zeval
from testlib import make_state
from universal import symbolic_start


def test_transaction_evaluate() -> None:
    state = make_state()
    solver = Solver()
    state.constrain(solver)
    assert solver.check()

    values = state.transaction.evaluate(solver.model())
    assert values == {
        "Caller": "0xcacacacacacacacacacacacacacacacacacacaca",
        "Gas": "0x0000000000000000000000000000000000000000000000000000000000000012",
    }


def test_transfer() -> None:
    start = symbolic_start(disassemble(b""), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = BA(0x1234), BA(0x5678)

    end.universe.transfer(src, dst, BW(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.assert_and_track(start.universe.balances[src] == 0xAAA, "TEST1")
    solver.assert_and_track(start.universe.balances[dst] == 0x0, "TEST2")
    assert solver.check()

    model = solver.model()
    assert zeval(model, end.universe.balances[src]) == 0x9AA
    assert zeval(model, end.universe.balances[dst]) == 0x100


def test_impossible_transfer() -> None:
    start = symbolic_start(disassemble(b""), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = BA(0x1234), BA(0x5678)

    end.universe.transfer(src, dst, BW(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.assert_and_track(z3.ULE(start.universe.balances[src], 0xF), "TEST1")
    assert not solver.check()
