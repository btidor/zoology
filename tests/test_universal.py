#!/usr/bin/env pytest

from typing import Any

import pytest

import tests.fixtures as cases
from disassembler import Program, disassemble
from sha3 import SHA3
from smt import Uint160, Uint256
from solidity import abiencode, load_binary, load_solidity, loads_solidity
from solver import Solver
from state import State, Termination
from universal import (
    _universal_transaction,
    constrain_to_goal,
    printable_transition,
    symbolic_start,
    universal_transaction,
)


def check_transitions(start: Program | State, branches: tuple[Any, ...]) -> None:
    if isinstance(start, Program):
        start = symbolic_start(start, SHA3(), "")

    expected = dict((b[0], b[1:]) for b in branches)
    for end in _universal_transaction(start):
        assert end.px() in expected, f"unexpected path: {end.px()}"
        assert isinstance(end.pc, Termination)
        assert end.pc.success is True

        kind, method, value = (expected[end.px()] + (None,))[:3]

        solver = Solver()
        end.constrain(solver)
        constrain_to_goal(solver, start, end)
        assert solver.check() == (kind == "GOAL")

        if kind != "GOAL":
            assert end.is_changed(start) == (kind == "SAVE")

        solver = Solver()
        end.constrain(solver)
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
    code = bytes.fromhex("60FF60EE5560AA60AA03600E57005B60006000FD")
    program = disassemble(code)
    sha3 = SHA3()

    universal = universal_transaction(program, sha3, "")

    start, end = next(universal)
    assert isinstance(end.pc, Termination)
    assert end.pc.success == True

    # These extra constraints makes the test deterministic
    end.path_constraints.append(
        start.universe.balances[Uint160(0xADADADADADADADADADADADADADADADADADADADAD)]
        == Uint256(0x8000000000001)
    )
    end.path_constraints.append(
        start.universe.balances[Uint160(0xCACACACACACACACACACACACACACACACACACACACA)]
        == Uint256(0xAAAAAAAAAAAAA)
    )
    solver = Solver()
    end.constrain(solver)
    constrain_to_goal(solver, start, end)
    assert not solver.check()

    solver = Solver()
    end.constrain(solver)
    assert solver.check()

    raw = """
        ---  📒 SAVE\tRETURN\tPx2\t---------------------------------------------------------

        Caller\t0xcacacacacacacacacacacacacacacacacacacaca

        Address\t0xadadadadadadadadadadadadadadadadadadadad

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
