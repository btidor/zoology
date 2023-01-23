#!/usr/bin/env pytest

import copy
from typing import Any, Tuple, Union

import test_entcommon as cases
from disassembler import Program
from state import State
from testlib import Benchmark, check_paths, load_binary, load_solidity, loads_solidity


def bench(
    benchmark: Benchmark,
    input: Union[Program, State],
    branches: Tuple[Tuple[Any, ...], ...],
) -> None:
    expected = frozenset(b[0] for b in branches)
    benchmark.pedantic(
        check_paths,
        setup=lambda: (
            (input if isinstance(input, Program) else copy.deepcopy(input), expected),
            {},
        ),
        rounds=1,
    )


def test_fallback(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/01_Fallback.sol")
    bench(benchmark, program, cases.Fallback)


def test_fallout(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/02_Fallout.sol")
    bench(benchmark, program, cases.Fallout)


def test_coinflip(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/03_CoinFlip.sol")
    bench(benchmark, program, cases.CoinFlip)


def test_telephone(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/04_Telephone.sol")
    bench(benchmark, program, cases.Telephone)


def test_token(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/05_Token.sol")
    bench(benchmark, program, cases.Token)


def test_delegation(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/06_Delegation.sol")
    start = cases.delegation_start(programs)
    bench(benchmark, start, cases.Delegation)


def test_force(benchmark: Benchmark) -> None:
    program = load_binary("ethernaut/07_Force.bin")
    bench(benchmark, program, cases.Force)


def test_vault(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/08_Vault.sol")
    bench(benchmark, program, cases.Vault)


def test_king(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/09_King.sol")
    bench(benchmark, program, cases.King)


def test_reentrancy(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/10_Reentrancy.sol")
    bench(benchmark, program, cases.Reentrancy)


def test_elevator(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/11_Elevator.sol")
    bench(benchmark, programs["Elevator"], cases.Elevator)


def test_privacy(benchmark: Benchmark) -> None:
    program = load_binary("ethernaut/12_Privacy.bin")
    bench(benchmark, program, cases.Privacy)


def test_gatekeeper_one(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/13_GatekeeperOne.sol")
    bench(benchmark, program, cases.GatekeeperOne)


def test_gatekeeper_two(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/14_GatekeeperTwo.sol")
    bench(benchmark, program, cases.GatekeeperTwo)


def test_preservation(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/15_Preservation.sol")
    start = cases.preservation_start(programs)
    bench(benchmark, start, cases.Preservation)
