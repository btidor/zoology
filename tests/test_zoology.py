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
    factory = LEVEL_FACTORIES[i]
    universe = starting_universe(factory)

    instance, beginning = createInstance(universe, factory)
    validator = validateInstance(factory, instance, beginning)
    solver = constrainWithValidator(factory, instance, beginning, validator)
    assert not solver.check(), "validation passed initially"

    result = search(factory, instance, beginning, validator, depth=10)
    assert result is not None, "search failed"

    solution, solver = result
    for actual, expected in zip(solution.describe(solver), fixture, strict=True):
        assert actual == expected


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
    fixture = [
        "PxB\t6fab5ddf",
    ]
    check_level(2, fixture)


def test_coinflip() -> None:
    fixture = [
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
    ]
    check_level(3, fixture)


def test_telephone() -> None:
    fixture = [
        "PxCE\ta6f9dae1 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca\t(via proxy)",
    ]
    check_level(4, fixture)


def test_token() -> None:
    fixture = [
        "Px63\ta9059cbb ffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacaca0000000000000000000000000000000000000000000000000000000000000001\t(via proxy)",
    ]
    check_level(5, fixture)


def test_delegation() -> None:
    fixture = [
        "Px193\tdd365b8b",
    ]
    check_level(6, fixture)


def test_force() -> None:
    fixture = [
        "SELFDESTRUCT\t(value: 1)",
    ]
    check_level(7, fixture)


def test_vault() -> None:
    fixture = [
        "Px66\tec9b5b3a 412076657279207374726f6e67207365637265742070617373776f7264203a29",
    ]
    check_level(8, fixture)


def test_king() -> None:
    fixture = [
        "PxDD\t(empty) \t(value: 1125899906842623, via proxy)",
    ]
    check_level(9, fixture)


# def test_reentrance() -> None:
#     # reentrance not supported
#     check_level(10, [])


def test_elevator() -> None:
    fixture = [
        "Px19F7\ted9a7134 00000000000000000000000000000000000000000000000000000001000000ff\t(via proxy)",
    ]
    check_level(11, fixture)


def test_privacy() -> None:
    fixture = [
        "Px18F\te1afb08c 8d3e0f3be93413600f15f3408ac39e7000000000000000000000000000000000",
    ]
    check_level(12, fixture)


def test_gatekeeper_one() -> None:
    fixture = [
        "PxDFF\t3370204e 000000010000caca000000000000000000000000000000000000000000000000\t(via proxy)",
    ]
    check_level(13, fixture)


def test_gatekeeper_two() -> None:
    fixture = [
        "Px1BF\t3370204e 2433b6aeb6cc3764000000000000000000000000000000000000000000000000\t(via proxy)",
    ]
    check_level(14, fixture)


def test_naughtcoin() -> None:
    fixture = [
        "Px6DF\t095ea7b3 000000000000000000000000cacacacacacacacacacacacacacacacacacacacaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "Px35FF\t23b872dd 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca000000000000000000000000cacacacacacacacacacacacacacacacacacacacb00000000000000000000000000000000000000000000d3c21bcecceda1000000",
    ]
    check_level(15, fixture)


def test_preservation() -> None:
    fixture = [
        "Px6657\t5bda8fa4 ffffffffffffffffffffffffc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
        "Px1864\tf1e02620 ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000",
        "\tProxy RETURN 00",
        "\tSet 0x3 to 0x1",
        "\tSet 0x2 to 0xcacacacacacacacacacacacacacacacacacacaca",
    ]
    check_level(16, fixture)


# def test_recovery() -> None:
#     # CREATE requires concrete program data / interacting with wrong contract
#     check_level(17, [])


def test_magic_number() -> None:
    fixture = [
        "Px37\t1f879433 0000000000000000000000000000000000000000000000000000000000000000",
    ]
    check_level(18, fixture)


def test_alien_codex() -> None:
    fixture = [
        "Px6D\t328b52cb",
        "Px1A7\t47f57b32",
        "Px1BF\t0339f300 4ef1d2ad89edf8c4d91132028e8195cdf30bb4b5053d4f8cd260341d4805f30a000000000000000000000001cacacacacacacacacacacacacacacacacacacaca",
    ]
    check_level(19, fixture)


def test_denial() -> None:
    fixture = [
        "PxAF\t4e1c5914 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
        "\tProxy CONSUME ALL GAS",
    ]
    check_level(20, fixture)


def test_shop() -> None:
    # TODO: illustrate proxy calls
    fixture = [
        "Px673\ta6f2ae3a\t(via proxy)",
    ]
    check_level(21, fixture)


# def test_dex() -> None:
#     # read-only check ignores token contract storage changes
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

# def test_switch() -> None:
#     check_level(29, [])
