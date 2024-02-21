#!/usr/bin/env pytest

from snapshot import LEVEL_FACTORIES, snapshot_contracts
from zoology import (
    constrainWithValidator,
    createInstance,
    search,
    validateInstance,
)


def check_level(i: int, fixture: list[str]) -> None:
    factory = LEVEL_FACTORIES[i]
    contracts = snapshot_contracts(factory)

    instance, beginning = createInstance(contracts, factory)
    validator = validateInstance(factory, instance, beginning)
    solver = constrainWithValidator(factory, instance, beginning, validator)
    assert not solver.check(), "validation passed initially"

    result = search(factory, instance, beginning, validator, depth=10)
    assert result is not None, "search failed"

    solution, solver = result
    assert "".join(solution.describe(solver)).strip() == "\n".join(fixture)


# def test_hello() -> None:
#     # Gets stuck exploring abi.encodePacked(...) with symbolic input
#     check_level(0, [])


def test_fallback() -> None:
    fixture = [
        "d7bb99ba\tvalue: 1",
        "-       \tvalue: 1",
        "3ccfd60b",
    ]
    check_level(1, fixture)


def test_fallout() -> None:
    fixture = [
        "6fab5ddf",
    ]
    check_level(2, fixture)


def test_coinflip() -> None:
    fixture = [
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
        "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
    ]
    check_level(3, fixture)


def test_telephone() -> None:
    fixture = [
        "a6f9dae1 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca\tvia proxy",
    ]
    check_level(4, fixture)


def test_token() -> None:
    fixture = [
        "a9059cbb ffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacaca0000000000000000000000000000000000000000000000000000000000000001\tvia proxy",
    ]
    check_level(5, fixture)


def test_delegation() -> None:
    fixture = [
        "dd365b8b",
    ]
    check_level(6, fixture)


def test_force() -> None:
    fixture = [
        "SELFDESTRUCT\tvalue: 1",
    ]
    check_level(7, fixture)


def test_vault() -> None:
    fixture = [
        "ec9b5b3a 412076657279207374726f6e67207365637265742070617373776f7264203a29",
    ]
    check_level(8, fixture)


def test_king() -> None:
    fixture = [
        "-       \tvalue: 1125899906842623\tvia proxy",
    ]
    check_level(9, fixture)


# def test_reentrance() -> None:
#     # reentrance not supported
#     check_level(10, [])


def test_elevator() -> None:
    fixture = [
        "ed9a7134 00000000000000000000000000000000000000000000000000000001000000ff\tvia proxy",
    ]
    check_level(11, fixture)


def test_privacy() -> None:
    fixture = [
        "e1afb08c 8d3e0f3be93413600f15f3408ac39e7000000000000000000000000000000000",
    ]
    check_level(12, fixture)


def test_gatekeeper_one() -> None:
    fixture = [
        "3370204e 000000010000caca000000000000000000000000000000000000000000000000\tvia proxy",
    ]
    check_level(13, fixture)


def test_gatekeeper_two() -> None:
    fixture = [
        "3370204e 2433b6aeb6cc3764000000000000000000000000000000000000000000000000\tvia proxy",
    ]
    check_level(14, fixture)


def test_naughtcoin() -> None:
    fixture = [
        "095ea7b3 000000000000000000000000cacacacacacacacacacacacacacacacacacacacaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "23b872dd 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca000000000000000000000000cacacacacacacacacacacacacacacacacacacacb00000000000000000000000000000000000000000000d3c21bcecceda1000000",
    ]
    check_level(15, fixture)


def test_preservation() -> None:
    fixture = [
        "5bda8fa4 ffffffffffffffffffffffffc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
        "f1e02620 ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000",
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
        "1f879433 0000000000000000000000000000000000000000000000000000000000000000",
    ]
    check_level(18, fixture)


def test_alien_codex() -> None:
    fixture = [
        "328b52cb",
        "47f57b32",
        "0339f300 4ef1d2ad89edf8c4d91132028e8195cdf30bb4b5053d4f8cd260341d4805f30a000000000000000000000001cacacacacacacacacacacacacacacacacacacaca",
    ]
    check_level(19, fixture)


def test_denial() -> None:
    fixture = [
        "4e1c5914 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
        "\tProxy CONSUME ALL GAS",
    ]
    check_level(20, fixture)


def test_shop() -> None:
    # TODO: illustrate proxy calls
    fixture = [
        "a6f2ae3a\tvia proxy",
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
