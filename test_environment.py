#!/usr/bin/env pytest

import copy

from disassembler import disassemble
from sha3 import SHA3
from smt import Uint160, Uint256
from solver import Solver
from testlib import concretize, make_state
from universal import symbolic_start


def test_transaction_evaluate() -> None:
    state = make_state()
    solver = Solver()
    state.constrain(solver)
    assert solver.check()

    values = state.transaction.evaluate(solver)
    assert values == {
        "Caller": "0xcacacacacacacacacacacacacacacacacacacaca",
        "Gas": "0x0000000000000000000000000000000000000000000000000000000000000012",
    }


def test_transfer() -> None:
    start = symbolic_start(disassemble(b""), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = Uint160(0x1234), Uint160(0x5678)

    end.universe.transfer(src, dst, Uint256(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.assert_and_track(start.universe.balances[src] == Uint256(0xAAA))
    solver.assert_and_track(start.universe.balances[dst] == Uint256(0x0))
    assert solver.check()

    assert concretize(solver.evaluate(end.universe.balances[src])) == 0x9AA
    assert concretize(solver.evaluate(end.universe.balances[dst])) == 0x100


def test_impossible_transfer() -> None:
    start = symbolic_start(disassemble(b""), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = Uint160(0x1234), Uint160(0x5678)

    end.universe.transfer(src, dst, Uint256(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.assert_and_track(start.universe.balances[src] <= Uint256(0xF))
    assert not solver.check()
