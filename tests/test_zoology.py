#!/usr/bin/env pytest

from snapshot import LEVEL_FACTORIES
from zoology import (
    constrainWithValidator,
    createInstance,
    search,
    starting_universe,
    validateInstance,
)


def check_level(i: int, fixture: list[str]) -> None:
    universe = starting_universe()
    factory = LEVEL_FACTORIES[i]

    instance, beginning = createInstance(universe, factory)
    validator = validateInstance(factory, instance, beginning)
    solver = constrainWithValidator(factory, instance, beginning, validator)
    assert not solver.check()

    result = search(factory, instance, beginning, validator, 10)
    assert result is not None

    solution, solver = result
    for actual, expected in zip(solution.describe(solver), fixture, strict=True):
        assert actual == expected


def test_starting_universe() -> None:
    # benchmark for profiling
    starting_universe()
    starting_universe()


# def test_hello() -> None:
#     # Gets stuck exploring abi.encodePacked(...) with symbolic input
#     check_level(0, [])


def test_fallback() -> None:
    fixture = [
        "Px8F\td7bb99ba\t(value: 1)",
        "Px19\t(empty) \t(value: 1)",
        "Px5F\t3ccfd60b",
    ]
    check_level(1, fixture)


def test_fallout() -> None:
    fixture = ["PxB\t6fab5ddf"]
    check_level(2, fixture)


def test_coinflip() -> None:
    check_level(
        3,
        [
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDFD\t1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
            "PxDFD\t1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDFD\t1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
            "PxDF9\t1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        ],
    )


def test_telephone() -> None:
    fixture = [
        "PxCE\ta6f9dae1 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca\t(via proxy)"
    ]
    check_level(4, fixture)


def test_token() -> None:
    fixture = [
        "Px63\ta9059cbb ffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacacb4000000000000000000000000000000000000000000000000000000000000000"
    ]
    check_level(5, fixture)


# def test_delegation() -> None:
#     check_level(6, [])


# def test_force() -> None:
#     # balance changes via SELFDESTRUCT are not supported
#     check_level(7, [])


def test_vault() -> None:
    fixture = [
        "Px66\tec9b5b3a 412076657279207374726f6e67207365637265742070617373776f7264203a29"
    ]
    check_level(8, fixture)


def test_king() -> None:
    fixture = ["PxDD\t(empty) \t(value: 1125899906842623, via proxy)"]
    check_level(9, fixture)


# def test_reentrancy() -> None:
#     check_level(10, [])


def test_elevator() -> None:
    fixture = [
        "Px19F7\ted9a7134 ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\t(via proxy)"
    ]
    check_level(11, fixture)


def test_privacy() -> None:
    fixture = [
        "Px18F\te1afb08c 8d3e0f3be93413600f15f3408ac39e7000000000000000000000000000000000"
    ]
    check_level(12, fixture)


def test_gatekeeper_one() -> None:
    fixture = [
        "PxDFF\t3370204e 000000010000caca000000000000000000000000000000000000000000000000\t(via proxy)"
    ]
    check_level(13, fixture)


def test_gatekeeper_two() -> None:
    fixture = [
        "Px1BF\t3370204e 2433b6aeb6cc3764000000000000000000000000000000000000000000000000\t(via proxy)"
    ]
    check_level(14, fixture)


# def test_naughtcoin() -> None:
#     check_level(15, [])


# def test_preservation() -> None:
#     check_level(16, [])


# def test_recovery() -> None:
#     check_level(17, [])


def test_magic_number() -> None:
    fixture = [
        "Px37\t1f879433 000000000000000000000000ffffffffffffffffffffffffffffffffffffffff"
    ]
    check_level(18, fixture)


# def test_alien_codex() -> None:
#     check_level(19, [])


# def test_denial() -> None:
#     check_level(20, [])


def test_shop() -> None:
    fixture = ["Px673\ta6f2ae3a\t(via proxy)"]
    check_level(21, fixture)


# def test_dex() -> None:
#     check_level(22, [])


# def test_dex2() -> None:
#     check_level(23, [])


# def test_puzzle_wallet() -> None:
#     check_level(24, [])


# def test_motorbike() -> None:
#     check_level(25, [])


# def test_double_entry_point() -> None:
#     check_level(26, [])


# def test_good_samaritan() -> None:
#     check_level(27, [])


# def test_gatekeeper_three() -> None:
#     check_level(28, [])
