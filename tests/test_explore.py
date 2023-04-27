#!/usr/bin/env pytest

from typing import Any

import tests.fixtures as cases
from disassembler import Program
from smt.sha3 import SHA3
from solidity import load_binary, load_solidity, loads_solidity
from state import State
from universal import _universal_transaction, symbolic_start


def check_paths(input: Program | State, branches: tuple[Any, ...]) -> None:
    expected = set(b[0] for b in branches)
    if isinstance(input, Program):
        input = symbolic_start(input, SHA3(), "")
    actual = set()
    for end in _universal_transaction(input):
        assert end.px() not in actual, "duplicate path"
        actual.add(end.px())
    assert actual == expected


def test_fallback() -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    check_paths(program, cases.Fallback)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    check_paths(program, cases.Fallout)


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    check_paths(program, cases.CoinFlip)


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    check_paths(program, cases.Telephone)


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    check_paths(program, cases.Token)


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")
    start = cases.delegation_start(programs)
    check_paths(start, cases.Delegation)


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    check_paths(program, cases.Force)


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    check_paths(program, cases.Vault)


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    check_paths(program, cases.King)


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    check_paths(program, cases.Reentrancy)


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")
    check_paths(programs["Elevator"], cases.Elevator)


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    check_paths(program, cases.Privacy)


def test_gatekeeper_one() -> None:
    program = load_solidity("fixtures/13_GatekeeperOne.sol")
    check_paths(program, cases.GatekeeperOne)


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    check_paths(program, cases.GatekeeperTwo)


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    start = cases.preservation_start(programs)
    check_paths(start, cases.Preservation)
