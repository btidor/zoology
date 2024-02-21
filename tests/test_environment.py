#!/usr/bin/env pytest

import copy

from bytes import Bytes
from disassembler import disassemble
from sha3 import SHA3
from smt import Solver, Uint160, Uint256
from state import State
from universal import symbolic_start


def test_transaction_evaluate() -> None:
    state = State()
    solver = Solver()
    state.constrain(solver)
    assert solver.check()

    values = state.transaction.describe(solver)
    assert values == {
        "Caller": "0xcacacacacacacacacacacacacacacacacacacaca",
        "Gas": "0x0000000000000000000000000000000000000000000000000000000000000012",
    }


def test_transfer() -> None:
    start = symbolic_start(disassemble(Bytes()), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = Uint160(0x1234), Uint160(0x5678)

    end.transfer(src, dst, Uint256(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.add(start.balances[src] == Uint256(0xAAA))
    solver.add(start.balances[dst] == Uint256(0x0))
    assert solver.check()

    assert solver.evaluate(end.balances[src]) == 0x9AA
    assert solver.evaluate(end.balances[dst]) == 0x100


def test_impossible_transfer() -> None:
    start = symbolic_start(disassemble(Bytes()), SHA3(), "")
    end = copy.deepcopy(start)
    src, dst = Uint160(0x1234), Uint160(0x5678)

    end.transfer(src, dst, Uint256(0x100))

    solver = Solver()
    end.constrain(solver)
    solver.add(start.balances[src] <= Uint256(0xF))
    assert not solver.check()
