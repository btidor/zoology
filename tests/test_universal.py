#!/usr/bin/env pytest

import copy
from typing import Any

import pytest

from bytes import Bytes
from disassembler import Program, abiencode, disassemble
from sha3 import SHA3
from smt import Solver, Uint160, Uint256
from state import State, Termination
from universal import printable_transition, symbolic_start, universal_transaction

from . import helpers as cases
from .solidity import load_binary, load_solidity, loads_solidity


def check_transitions(start: Program | State, branches: tuple[Any, ...]) -> None:
    if isinstance(start, Program):
        start = symbolic_start(start, SHA3(), "")
    start.skip_self_calls = True

    expected = dict((b[0], b[1:]) for b in branches)
    for end in universal_transaction(start):
        assert end.px() in expected, f"unexpected path: {end.px()}"
        assert isinstance(end.pc, Termination)
        assert end.pc.success is True

        kind, method, value = (expected[end.px()] + (None,))[:3]

        solver = Solver()
        solver.add(end.constraint)
        assert end.changed == (kind == "SAVE")

        assert solver.check()
        end.narrow(solver)
        transaction = end.transaction.describe(solver)

        actual = bytes.fromhex(transaction.get("Data", "")[2:10])
        if method is None:
            assert actual == b"", f"unexpected data: {actual.hex()}"
        elif method.startswith("0x"):
            assert actual == bytes.fromhex(
                method[2:]
            ), f"unexpected data: {actual.hex()}"
        elif method == "$any4":
            assert len(actual) == 4, f"unexpected data: {actual.hex()}"
        else:
            assert actual == abiencode(method), f"unexpected data: {actual.hex()}"

        if "Value" not in transaction:
            assert value is None
        else:
            assert value is not None
            assert transaction["Value"] == "0x" + int.to_bytes(value, 32).hex()

        del expected[end.px()]

    assert len(expected) == 0, f"missing paths: {expected.keys()}"


def test_basic() -> None:
    code = Bytes.fromhex("60FF60EE5560AA60AA03600E57005B60006000FD")
    program = disassemble(code)

    start = symbolic_start(program, SHA3(), "")
    init = copy.deepcopy(start)
    init.transfer(
        init.transaction.caller,
        init.transaction.address,
        init.transaction.callvalue,
    )
    universal = universal_transaction(init)

    end = next(universal)
    assert isinstance(end.pc, Termination)
    assert end.pc.success is True

    # These extra constraints makes the test deterministic
    end.constraint &= start.balances[
        Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
    ] == Uint256(0x8000000000001)
    end.constraint &= start.balances[
        Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    ] == Uint256(0xAAAAAAAAAAAAA)

    solver = Solver()
    solver.add(end.constraint)
    assert solver.check()

    raw = """
        ---  📒 SAVE\tRETURN\tPx2\t---------------------------------------------------------

        Caller\t0xcacacacacacacacacacacacacacacacacacacaca

        Balance\tR: 0xadadadadadadadadadadadadadadadadadadadad
        \t-> 0x8000000000001
        \tR: 0xcacacacacacacacacacacacacacacacacacacaca
        \t-> 0xaaaaaaaaaaaaa

        Storage\tW: 0xee -> 0xff (from 0x0)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:])

    for actual, expected in zip(printable_transition(start, end), fixture, strict=True):
        assert actual.strip(" ") == expected

    with pytest.raises(StopIteration):
        next(universal)


def test_sudoku() -> None:
    program = load_solidity("fixtures/99_Sudoku.sol")

    start = symbolic_start(program, SHA3(), "")
    universal = universal_transaction(start)

    end = next(universal)
    assert isinstance(end.pc, Termination)
    assert end.pc.success is True

    solver = Solver()
    solver.add(end.constraint)
    assert solver.check()

    calldata = end.transaction.calldata
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

    with pytest.raises(StopIteration):
        next(universal)


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


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")
    start = cases.delegation_start(programs)
    check_transitions(start, cases.Delegation)


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


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    start = cases.preservation_start(programs)
    check_transitions(start, cases.Preservation)
