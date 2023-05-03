#!/usr/bin/env pytest

from typing import Iterable

from snapshot import LEVEL_FACTORIES
from zoology import createInstance, search, starting_universe, validateInstance


def check_level(i: int) -> Iterable[str]:
    universe = starting_universe()
    factory = LEVEL_FACTORIES[i]

    instance, beginning = createInstance(universe, factory)
    for _, ok in validateInstance(factory, instance, beginning):
        assert ok.unwrap() is False

    result = search(factory, instance, beginning, 1)
    assert result is not None

    solution, ok = result
    yield from solution.describe(ok, skip_final=True)


def test_starting_universe() -> None:
    # benchmark for profiling
    starting_universe()
    starting_universe()


# def test_hello() -> None:
#     check_level(0)


# def test_fallback() -> None:
#     check_level(1)


def test_fallout() -> None:
    raw = """
        PxB\t6fab5ddf
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(2), fixture, strict=True):
        assert actual == expected


# def test_coinflip() -> None:
#     check_level(3)


def test_telephone() -> None:
    raw = """
        PxCE\ta6f9dae1 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca\t(via proxy)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(4), fixture, strict=True):
        assert actual == expected


def test_token() -> None:
    raw = """
        Px63\ta9059cbb ffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacacb4000000000000000000000000000000000000000000000000000000000000000
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(5), fixture, strict=True):
        assert actual == expected


# def test_delegation() -> None:
#     check_level(6)


# def test_force() -> None:
#     check_level(7)


def test_vault() -> None:
    raw = """
        Px66\tec9b5b3a 412076657279207374726f6e67207365637265742070617373776f7264203a29
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(8), fixture, strict=True):
        assert actual == expected


# def test_king() -> None:
#     check_level(9)


# def test_reentrancy() -> None:
#     check_level(10)


def test_elevator() -> None:
    raw = """
        Px19F7\ted9a7134 ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(11), fixture, strict=True):
        assert actual == expected


def test_privacy() -> None:
    raw = """
        Px18F\te1afb08c 8d3e0f3be93413600f15f3408ac39e7000000000000000000000000000000000
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(12), fixture, strict=True):
        assert actual == expected


def test_gatekeeper_one() -> None:
    raw = """
        PxDFF\t3370204e 000000010000caca000000000000000000000000000000000000000000000000\t(via proxy)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(13), fixture, strict=True):
        assert actual == expected


def test_gatekeeper_two() -> None:
    raw = """
        Px1BF\t3370204e 2433b6aeb6cc3764000000000000000000000000000000000000000000000000\t(via proxy)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(14), fixture, strict=True):
        assert actual == expected


# def test_naughtcoin() -> None:
#     check_level(15)


# def test_preservation() -> None:
#     check_level(16)


# def test_recovery() -> None:
#     check_level(17)


# def test_magic_number() -> None:
#     check_level(18)


# def test_alien_codex() -> None:
#     check_level(19)


# def test_denial() -> None:
#     check_level(20)


def test_shop() -> None:
    raw = """
        Px673\ta6f2ae3a
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:-1])

    for actual, expected in zip(check_level(21), fixture, strict=True):
        assert actual == expected


# def test_dex() -> None:
#     check_level(22)


# def test_dex2() -> None:
#     check_level(23)


# def test_puzzle_wallet() -> None:
#     check_level(24)


# def test_motorbike() -> None:
#     check_level(25)


# def test_double_entry_point() -> None:
#     check_level(26)


# def test_good_samaritan() -> None:
#     check_level(27)


# def test_gatekeeper_three() -> None:
#     check_level(28)
