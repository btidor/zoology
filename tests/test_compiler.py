#!/usr/bin/env pytest

from typing import Any

from compiler import compile, symbolic_transaction
from disassembler import Program, abiencode
from smt import Solver, Uint256

from .solidity import load_binary, load_solidity, loads_solidity

Fallback = (
    ("Px19", "SAVE", None, 1),
    ("PxB9", "SAVE", "withdraw()"),
    ("Px23", "VIEW", "owner()"),
    ("Px5F", "SAVE", "withdraw()"),
    ("Px4F", "VIEW", "contributions(address)"),
    ("Px83", "VIEW", "getContribution()"),
    ("Px10E", "SAVE", "contribute()"),
    ("Px10F", "SAVE", "contribute()"),
)

Fallout = (
    ("Px5", "SAVE", "Fal1out()"),
    ("Px23", "VIEW", "owner()"),
    ("Px139", "SAVE", "collectAllocations()"),
    ("Px9F", "SAVE", "collectAllocations()"),
    ("Px83", "SAVE", "allocate()"),
    ("Px10F9", "SAVE", "sendAllocation(address)"),
    ("Px87F", "SAVE", "sendAllocation(address)"),
    ("Px40F", "VIEW", "allocatorBalance(address)"),
)

CoinFlip = (
    ("Px6FF", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px6FD", "SAVE", "flip(bool)"),
    ("PxDF9", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px19", "VIEW", "consecutiveWins()"),
)

Telephone = (
    ("PxD", "VIEW", "owner()"),
    ("PxCF", "VIEW", "changeOwner(address)"),
    ("PxCE", "SAVE", "changeOwner(address)"),
)

Token = (
    ("PxD", "VIEW", "totalSupply()"),
    ("Px33", "VIEW", "balanceOf(address)"),
    ("PxC7", "SAVE", "transfer(address,uint256)"),
)

Delegation = (
    ("Px331", "VIEW", "$any4"),  # *
    ("Px333", "SAVE", "pwn()"),
    ("PxD", "VIEW", "owner()"),
    ("Px7F", "VIEW", None),  # *
    # * if Delegate reverts, Delegation will still return successfully
)

Force = ()

Vault = (
    ("PxD", "VIEW", "locked()"),
    ("PxCF", "VIEW", "unlock(bytes32)"),
    ("PxCE", "SAVE", "unlock(bytes32)"),
)

King = (
    ("PxB", "VIEW", "_king()"),
    ("Px13", "VIEW", "owner()"),
    ("PxC9", "SAVE", None, None),
    ("PxD9", "SAVE", None, None),
    ("Px23", "VIEW", "prize()"),
    ("Px6F", "SAVE", None, None),
    ("Px67", "SAVE", None, None),
)

Reentrancy = (
    ("Px6", "VIEW", None),
    ("Px2F", "SAVE", "donate(address)"),
    ("Px4F", "VIEW", "balances(address)"),
    ("Px11F", "VIEW", "withdraw(uint256)"),
    ("Px10F", "VIEW", "balanceOf(address)"),
    ("Px8F5", "SAVE", "withdraw(uint256)"),
    ("Px8F7", "SAVE", "withdraw(uint256)"),
    ("Px11E3", "SAVE", "withdraw(uint256)"),
    ("Px11E7", "SAVE", "withdraw(uint256)"),
)

Elevator = (
    ("PxD", "VIEW", "floor()"),
    ("Px31", "VIEW", "top()"),
    ("PxCFF", "VIEW", "goTo(uint256)"),
    ("PxCFEF", "SAVE", "goTo(uint256)"),
)

Privacy = (
    ("PxD", "VIEW", "ID()"),
    ("Px19", "VIEW", "locked()"),
    ("Px18F", "SAVE", "unlock(bytes16)"),
)

GatekeeperOne = (
    ("PxDFF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

GatekeeperTwo = (
    ("Px1BF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

Preservation = (
    ("PxC1CEF", "SAVE", "setFirstTime(uint256)"),
    ("Px61", "VIEW", "owner()"),
    ("Px31CEF", "SAVE", "setSecondTime(uint256)"),
    ("Px19", "VIEW", "timeZone1Library()"),
    ("PxD", "VIEW", "timeZone2Library()"),
)


def check_transitions(program: Program, branches: tuple[Any, ...]) -> None:
    expected = dict((b[0], b[1:]) for b in branches)
    for term in compile(program):
        if not term.success:
            continue
        assert term.path.px() in expected, f"unexpected path: {term.path.px()}"

        kind, method, value = (expected[term.path.px()] + (None,))[:3]
        if term.storage is None:
            assert kind == "VIEW"
        else:
            assert kind == "SAVE"

        solver = Solver()
        solver.add(term.path.constraint)
        assert solver.check()
        term.path.narrow(solver)

        itx = symbolic_transaction()
        itx.narrow(solver)

        actual = itx.calldata.evaluate(solver)[:4]
        if method is None:
            assert actual == b"", f"unexpected data: {actual.hex()}"
        elif method == "$any4":
            assert len(actual) == 4, f"unexpected data: {actual.hex()}"
        else:
            assert actual == abiencode(method), f"unexpected data: {actual.hex()}"

        actual = solver.evaluate(itx.callvalue)
        if actual == 0:
            assert value is None
        else:
            assert value == actual

        del expected[term.path.px()]

    assert len(expected) == 0, f"missing paths: {expected.keys()}"


def test_fallback() -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    check_transitions(program, Fallback)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    check_transitions(program, Fallout)


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    check_transitions(program, CoinFlip)


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    check_transitions(program, Telephone)


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    check_transitions(program, Token)


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")
    check_transitions(programs["Delegation"], Delegation)


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    check_transitions(program, Force)


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    check_transitions(program, Vault)


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    check_transitions(program, King)


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    check_transitions(program, Reentrancy)


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")
    check_transitions(programs["Elevator"], Elevator)


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    check_transitions(program, Privacy)


def test_gatekeeper_one() -> None:
    program = load_solidity("fixtures/13_GatekeeperOne.sol")
    check_transitions(program, GatekeeperOne)


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    check_transitions(program, GatekeeperTwo)


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    check_transitions(programs["Preservation"], Preservation)


def test_sudoku() -> None:
    program = load_solidity("fixtures/99_Sudoku.sol")
    termini = list(term for term in compile(program) if term.success)

    assert len(termini) == 1
    term = termini[0]

    solver = Solver()
    solver.add(term.path.constraint)
    assert solver.check()

    calldata = symbolic_transaction().calldata
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
