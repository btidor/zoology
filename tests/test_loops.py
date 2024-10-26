#!/usr/bin/env pytest

from heapq import heappop, heappush

from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import Descend, Jump, Termination, Unreachable
from vm import step
from zoology import make_heads, starting_sequence


def check_level(i: int) -> None:
    factory = LEVEL_FACTORIES[i]
    contracts = snapshot_contracts(factory)

    beginning = starting_sequence(contracts, factory)
    queue = make_heads(beginning)
    while queue:
        state = heappop(queue)
        while isinstance(state.pc, int):
            match step(state):
                case None:
                    continue
                case Jump(targets):
                    for target in targets:
                        heappush(queue, target)
                    break
                case Descend():
                    break  # don't analyze cross-contract calls
                case Unreachable():
                    break

        if isinstance(state.pc, Termination):
            assert state.recursion is None
            state.cleanup()


def test_hello() -> None:
    check_level(0)


def test_fallback() -> None:
    check_level(1)


def test_fallout() -> None:
    check_level(2)


def test_coinflip() -> None:
    check_level(3)


def test_telephone() -> None:
    check_level(4)


def test_token() -> None:
    check_level(5)


def test_delegation() -> None:
    check_level(6)


def test_force() -> None:
    check_level(7)


def test_vault() -> None:
    check_level(8)


def test_king() -> None:
    check_level(9)


def test_reentrance() -> None:
    check_level(10)


def test_elevator() -> None:
    check_level(11)


def test_privacy() -> None:
    check_level(12)


def test_gatekeeper_one() -> None:
    check_level(13)


def test_gatekeeper_two() -> None:
    check_level(14)


def test_naughtcoin() -> None:
    check_level(15)


def test_preservation() -> None:
    check_level(16)


# def test_recovery() -> None:
#     check_level(17)


def test_magic_number() -> None:
    check_level(18)


def test_alien_codex() -> None:
    check_level(19)


def test_denial() -> None:
    check_level(20)


def test_shop() -> None:
    check_level(21)


def test_dex() -> None:
    check_level(22)


def test_dex2() -> None:
    check_level(23)


def test_puzzle_wallet() -> None:
    check_level(24)


# def test_motorbike() -> None:
#     check_level(25)


def test_double_entry_point() -> None:
    check_level(26)


def test_good_samaritan() -> None:
    check_level(27)


def test_gatekeeper_three() -> None:
    check_level(28)


def test_switch() -> None:
    check_level(29)


def test_higher_order() -> None:
    check_level(30)


def test_stake() -> None:
    check_level(31)
