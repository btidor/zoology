from opcodes import *


def test_ADD() -> None:
    assert ADD(10, 10) == 20
    assert (
        ADD(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 1) == 0
    )


def test_MUL() -> None:
    assert MUL(10, 10) == 100
    assert (
        MUL(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2)
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert SUB(10, 10) == 0
    assert (
        SUB(0, 1) == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert DIV(10, 10) == 1
    assert DIV(1, 2) == 0
    assert DIV(10, 0) == 0


def test_SDIV() -> None:
    assert SDIV(10, 10) == 1
    assert (
        SDIV(
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        )
        == 2
    )
    assert SDIV(10, 0) == 0


def test_MOD() -> None:
    assert MOD(10, 3) == 1
    assert MOD(17, 5) == 2
    assert MOD(10, 0) == 0


def test_SMOD() -> None:
    assert SMOD(10, 3) == 1
    assert (
        SMOD(
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD,
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert SMOD(10, 0) == 0


def test_ADDMOD() -> None:
    assert ADDMOD(10, 10, 8) == 4
    assert (
        ADDMOD(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 2, 2)
        == 1
    )


def test_MULMOD() -> None:
    assert MULMOD(10, 10, 8) == 4
    assert (
        MULMOD(
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            12,
        )
        == 9
    )


def test_EXP() -> None:
    assert EXP(10, 2) == 100
    assert EXP(2, 2) == 4


def test_SIGNEXTEND() -> None:
    assert (
        SIGNEXTEND(0, 0xFF)
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        SIGNEXTEND(0, 0xAA)
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert SIGNEXTEND(0, 0x7F) == 0x7F


def test_LT() -> None:
    assert LT(9, 10) == 1
    assert LT(10, 10) == 0


def test_GT() -> None:
    assert GT(10, 9) == 1
    assert GT(10, 10) == 0


def test_SLT() -> None:
    assert (
        SLT(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 0) == 1
    )
    assert SLT(10, 10) == 0


def test_SGT() -> None:
    assert (
        SGT(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) == 1
    )
    assert SGT(10, 10) == 0


def test_EQ() -> None:
    assert EQ(10, 10) == 1
    assert EQ(10, 5) == 0


def test_ISZERO() -> None:
    assert ISZERO(10) == 0
    assert ISZERO(0) == 1


def test_AND() -> None:
    assert AND(0xF, 0xF) == 0xF
    assert AND(0xFF, 0) == 0


def test_OR() -> None:
    assert OR(0xF0, 0xF) == 0xFF
    assert OR(0xFF, 0xFF) == 0xFF


def test_XOR() -> None:
    assert XOR(0xF0, 0xF) == 0xFF
    assert XOR(0xFF, 0xFF) == 0


def test_NOT() -> None:
    assert NOT(0) == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF


def test_BYTE() -> None:
    assert BYTE(31, 0xFF) == 0xFF
    assert BYTE(30, 0xFF00) == 0xFF
    assert BYTE(30, 0xAABBCC) == 0xBB
    assert BYTE(123456, 0xAABBCC) == 0


def test_SHL() -> None:
    assert SHL(1, 1) == 2
    assert (
        SHL(4, 0xFF00000000000000000000000000000000000000000000000000000000000000)
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert SHR(1, 2) == 1
    assert SHR(4, 0xFF) == 0xF
    assert SHR(123, 0xAA) == 0


def test_SAR() -> None:
    assert SAR(1, 2) == 1
    assert (
        SAR(4, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0)
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
