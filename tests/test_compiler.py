#!/usr/bin/env pytest

from typing import Any

from compiler import compile
from disassembler import Program, abiencode
from smt import Solver, Uint256
from state import Terminus

from . import fixture as cases
from .solidity import load_binary, load_solidity, loads_solidity


def check_transitions(program: Program, branches: tuple[Any, ...]) -> None:
    expected = dict((b[0], b[1:]) for b in branches)
    for state in compile(program):
        assert isinstance(state.pc, Terminus)
        if not state.pc.success:
            continue
        assert state.px() in expected, f"unexpected path: {state.px()}"

        kind, method, value = (expected[state.px()] + (None,))[:3]
        if state.static:
            assert kind == "VIEW"
        else:
            assert kind == "SAVE"

        solver = Solver()
        solver.add(state.path)
        assert solver.check()
        state.narrow(solver)

        actual = state.transaction.calldata.evaluate(solver)[:4]
        if method is None:
            assert actual == b"", f"unexpected data: {actual.hex()}"
        elif method == "$any4":
            assert len(actual) == 4, f"unexpected data: {actual.hex()}"
        else:
            assert actual == abiencode(method), f"unexpected data: {actual.hex()}"

        actual = solver.evaluate(state.transaction.callvalue)
        if actual == 0:
            assert value is None
        else:
            assert value == actual

        del expected[state.px()]

    assert len(expected) == 0, f"missing paths: {expected.keys()}"


def test_fallback() -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    check_transitions(program, cases.Fallback)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    check_transitions(program, cases.Fallout)


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    check_transitions(program, cases.CoinFlip)


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    check_transitions(program, cases.Telephone)


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    check_transitions(program, cases.Token)


# def test_delegation() -> None:
#     programs = loads_solidity("fixtures/06_Delegation.sol")
#     start = cases.delegation_start(programs)
#     check_transitions(start, cases.Delegation)


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    check_transitions(program, cases.Force)


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    check_transitions(program, cases.Vault)


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    check_transitions(program, cases.King)


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    check_transitions(program, cases.Reentrancy)


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")
    check_transitions(programs["Elevator"], cases.Elevator)


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    check_transitions(program, cases.Privacy)


def test_gatekeeper_one() -> None:
    program = load_solidity("fixtures/13_GatekeeperOne.sol")
    check_transitions(program, cases.GatekeeperOne)


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    check_transitions(program, cases.GatekeeperTwo)


# def test_preservation() -> None:
#     programs = loads_solidity("fixtures/15_Preservation.sol")
#     start = cases.preservation_start(programs)
#     check_transitions(start, cases.Preservation)


def test_sudoku() -> None:
    program = load_solidity("fixtures/99_Sudoku.sol")
    states = list(
        state
        for state in compile(program)
        if isinstance(state.pc, Terminus) and state.pc.success
    )

    assert len(states) == 1
    state = states[0]

    solver = Solver()
    solver.add(state.path)
    assert solver.check()

    calldata = state.transaction.calldata
    method = bytes(solver.evaluate(calldata[Uint256(i)]) for i in range(4))
    assert method.hex() == abiencode("check(uint256[9][9])").hex()

    offset = 4
    actual = [[0 for _ in range(9)] for _ in range(9)]
    for i in range(9):
        for j in range(9):
            value = bytes(
                solver.evaluate(calldata[Uint256(offset + z)]) for z in range(32)
            )
            offset += 32
            actual[i][j] = int.from_bytes(value)

    expected = [
        [4, 5, 6, 2, 1, 8, 9, 7, 3],
        [8, 9, 2, 3, 6, 7, 5, 4, 1],
        [7, 3, 1, 4, 9, 5, 2, 6, 8],
        [1, 2, 9, 5, 8, 6, 4, 3, 7],
        [3, 4, 8, 7, 2, 1, 6, 9, 5],
        [5, 6, 7, 9, 3, 4, 1, 8, 2],
        [2, 8, 5, 6, 7, 9, 3, 1, 4],
        [6, 1, 4, 8, 5, 3, 7, 2, 9],
        [9, 7, 3, 1, 4, 2, 8, 5, 6],
    ]
    assert actual == expected
