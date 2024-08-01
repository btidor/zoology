#!/usr/bin/env pytest

from zoology import search


def check_level(i: int, fixture: list[str]) -> None:
    assert "".join(search(i)).strip() == "\n".join(fixture)


# def test_hello() -> None:
#     fixture = [
#         "aa613b29 "
#         + "0000000000000000000000000000000000000000000000000000000000000020"
#         + "000000000000000000000000000000000000000000000000000000000000000a"
#         + "65746865726e61757430"
#     ]
#     check_level(0, fixture)


# def test_fallback() -> None:
#     fixture = [
#         "d7bb99ba\tvalue: 1",
#         "-       \tvalue: 1",
#         "3ccfd60b",
#     ]
#     check_level(1, fixture)


def test_fallout() -> None:
    fixture = [
        "6fab5ddf",
    ]
    check_level(2, fixture)


# def test_coinflip() -> None:
#     fixture = [
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000001",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#         "1d263f67 0000000000000000000000000000000000000000000000000000000000000000",
#     ]
#     check_level(3, fixture)


# def test_telephone() -> None:
#     fixture = [
#         "a6f9dae1 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca\tvia proxy",
#     ]
#     check_level(4, fixture)


# def test_token() -> None:
#     # This is correct! To solve this level, the player must transfer at least 20
#     # tokens to any other address, causing an integer underflow. The recipient
#     # address is arbitrary, and our solver apparently produces it by adding 1 to
#     # the player address.
#     fixture = [
#         "a9059cbb 000000000000000000000000cacacacacacacacacacacacacacacacacacacacb"
#         "         4000000000000000000000000000000000000000000000000000000000000014",
#     ]
#     check_level(5, fixture)


# def test_delegation() -> None:
#     fixture = [
#         "dd365b8b",
#     ]
#     check_level(6, fixture)


# def test_force() -> None:
#     fixture = [
#         "SELFDESTRUCT\tvalue: 1",
#     ]
#     check_level(7, fixture)


def test_vault() -> None:
    fixture = [
        "ec9b5b3a 412076657279207374726f6e67207365637265742070617373776f7264203a29",
    ]
    check_level(8, fixture)


# def test_king() -> None:
#     fixture = [
#         "-       \tvalue: 1125899906842623\tvia proxy",
#         "validateInstance(...)",
#         " -> Proxy CALL -       ",
#         "    REVERT -",
#     ]
#     check_level(9, fixture)


# def test_reentrance() -> None:
#     fixture = [
#         "00362a95 ffffffffffffffffffffffffc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0\tvalue: 1125899906842623",
#         "2e1a7d4d 0000000000000000000000000000000000000000000000000003c67ea4c67f00\tvia proxy",
#         " -> Proxy CALL -       \tvalue: 1062672162782976",
#         "     -> To 0x79cf5bd9e06f09ace1ade01aedeac5c979b77d6c:",
#         "        CALL 2e1a7d4d 0000000000000000000000000000000000000000000000000003c700000000ff",
#         "         -> Proxy CALL -       \tvalue: 1063227744059647",
#         "            RETURN 00",
#         "        RETURN -       ",
#         "    RETURN -",
#     ]
#     check_level(10, fixture)


# def test_elevator() -> None:
#     fixture = [
#         "ed9a7134 0000000000000000000000000000000000000000000000000000000000000000\tvia proxy",
#         " -> Proxy CALL 5f9a4bca 0000000000000000000000000000000000000000000000000000000000000000",
#         "    RETURN 0000000000000000000000000000000000000000000000000000000000000000",
#         " -> Proxy CALL 5f9a4bca 0000000000000000000000000000000000000000000000000000000000000000",
#         "    RETURN 0000000000000000000000000000000000000000000000000000000000000001",
#     ]
#     check_level(11, fixture)


def test_privacy() -> None:
    fixture = [
        "e1afb08c 2b6ef608f85e68b5df07df2f197c522100000000000000000000000000000000",
    ]
    check_level(12, fixture)


def test_gatekeeper_one() -> None:
    fixture = [
        "3370204e 000000010000c0c0000000000000000000000000000000000000000000000000\tvia proxy",
    ]
    check_level(13, fixture)


# def test_gatekeeper_two() -> None:
#     fixture = [
#         "Proxy CODESIZE 0x0 (via constructor)",
#         "3370204e 2433b6aeb6cc3764000000000000000000000000000000000000000000000000\tvia proxy",
#     ]
#     check_level(14, fixture)


# def test_naughtcoin() -> None:
#     fixture = [
#         "095ea7b3 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca"
#         + "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
#         "23b872dd 000000000000000000000000cacacacacacacacacacacacacacacacacacacaca"
#         + "0000000000000000000000008acacacacacacacacacacacacacacacacacacacf"
#         + "00000000000000000000000000000000000000000000d3c21bcecceda1000000",
#     ]
#     check_level(15, fixture)


# def test_preservation() -> None:
#     fixture = [
#         "5bda8fa4 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
#         "f1e02620 0000000000000000000000000000000000000000000000000000000000000000",
#         " -> Proxy DELEGATECALL 3beb26c4 0000000000000000000000000000000000000000000000000000000000000000",
#         "    RETURN 00",
#         "      0x2 -> 0xffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacaca",
#     ]
#     check_level(16, fixture)


# def test_recovery() -> None:
#     fixture = [
#         "To 0xfab8648a23eebdd484c15aaeebba94e17ac78129:",
#         "    00f55d9d 000000000000000000000000af98ab8f2e2b24f42c661ed023237f5b7acab049",
#     ]
#     check_level(17, fixture)


# def test_magic_number() -> None:
#     fixture = [
#         "Proxy CODESIZE 0x9",
#         "1f879433 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
#         "validateInstance(...)",
#         " -> Proxy CALL 650500c1",
#         "    RETURN 000000000000000000000000000000000000000000000000000000000000002a",
#     ]
#     check_level(18, fixture)


# def test_alien_codex() -> None:
#     fixture = [
#         "328b52cb",
#         "47f57b32",
#         "0339f300 4ef1d2ad89edf8c4d91132028e8195cdf30bb4b5053d4f8cd260341d4805f30a"
#         + "ffffffffffffffffffffffffcacacacacacacacacacacacacacacacacacacaca",
#     ]
#     check_level(19, fixture)


# def test_denial() -> None:
#     fixture = [
#         "4e1c5914 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0",
#         "validateInstance(...)",
#         " -> Proxy CALL -       \tvalue: 10000000000000",
#         "    CONSUME ALL GAS",
#     ]
#     check_level(20, fixture)


# def test_shop() -> None:
#     fixture = [
#         "a6f2ae3a\tvia proxy",
#         " -> Proxy CALL a035b1fe",
#         "    RETURN 0080000000000000000000000000000000000000000000000000000000000033",
#         " -> Proxy CALL a035b1fe",
#         "    RETURN 0000000000000000000000000000000000000000000000000000000000000000",
#     ]
#     check_level(21, fixture)


# def test_dex() -> None:
#     # slow + quadratic space
#     check_level(22, [])


# def test_dex2() -> None:
#     # slow or infinite + needs multiple transactions
#     check_level(23, [])


# def test_puzzle_wallet() -> None:
#     # infinite loops + needs multiple transactions
#     check_level(24, [])


# def test_motorbike() -> None:
#     fixture = [
#         "To 0x42976789d3e2613934d9386f952bea594f8f4a54:",
#         "    8129fc1c",
#         "To 0x42976789d3e2613934d9386f952bea594f8f4a54:",
#         "    4f1ef286 000000000000000000000000c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0"
#         + "0000000000000000000000000000000000000000000000000000000000000040"
#         + "0000000000000000000000000000000000000000000000000000000000000001"
#         + "00",
#         " -> Proxy DELEGATECALL 00",
#         "    SELFDESTRUCT",
#     ]
#     check_level(25, fixture)


# def test_double_entry_point() -> None:
#     # Nontraditional solution: attempting to invoke a method on an EOA address
#     # causes a revert, even inside a try/catch block:
#     # https://github.com/ethereum/solidity/issues/12725
#     fixture = [
#         "To 0x01a11621db21dd3eb323ada87bbb1d0d8a099544:",
#         "    9e927c68 0000000000000000000000000000000000000000000000000000000000000001",
#     ]
#     check_level(26, fixture)


# def test_good_samaritan() -> None:
#     fixture = [
#         "25143638\tvia proxy",
#         " -> Proxy CALL 98d078b4 000000000000000000000000000000000000000000000000000000000000000a",
#         "    REVERT ad3a8b9e",
#         " -> Proxy CALL 98d078b4 00000000000000000000000000000000000000000000000000000000000f4240",
#         "    RETURN -",
#     ]
#     check_level(27, fixture)


# def test_gatekeeper_three() -> None:
#     fixture = [
#         "b9966e56\tvia proxy",
#         "f7edf099",
#         "c960174e 00000000000000000000000000000000000000000000000000000000637e3113",
#         "SELFDESTRUCT\tvalue: 1125899906842623",
#         "e97dcb62\tvia proxy",
#         " -> Proxy CALL -       \tvalue: 1000000000000000",
#         "    REVERT -",
#     ]
#     check_level(28, fixture)


# def test_switch() -> None:
#     fixture = [
#         "30c13ade "
#         + "0000000000000000000000000000000000000000000000000000000000000044"
#         + "7622ff1500000000000000000000000000000000000000000000000000000044"
#         + "20606e1500000000000000000000000000000000000000000000000000000000"
#         + "0000000476227e12"
#     ]
#     check_level(29, fixture)


# def test_higher_order() -> None:
#     fixture = [
#         "211c85ab 80000000000000000000000000000000000000000000000000000000000000ff",
#         "5b3e8fe7",
#     ]
#     check_level(30, fixture)


# def test_stake() -> None:
#     check_level(31, [])
