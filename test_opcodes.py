import typing

from opcodes import *


class DummyWorld(World):
    def __init__(
        self,
        balances: typing.Dict[Address, uint256] = {},
        codes: typing.Dict[Address, bytes] = {},
    ):
        self.balances = balances
        self.codes = codes

    def balance(self, address: Address) -> uint256:
        return self.balances.get(address, 0)

    def code(self, address: Address) -> bytes:
        return self.codes.get(address, b"")


def _dump_memory(s: State) -> str:
    v = ""
    lim = max(s.memory.keys())
    for i in range(lim + 1):
        v += s.memory[i].to_bytes(1, "big").hex()
    return "0x" + v.upper()


def test_STOP() -> None:
    s = State(pc=123)
    STOP(s)
    assert s.pc == None


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


def test_SHA3() -> None:
    s = State(memory={0: 0xFF, 1: 0xFF, 2: 0xFF, 3: 0xFF})
    assert (
        SHA3(s, 0, 4)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    s = State(address=0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    assert ADDRESS(s) == s.address


def test_BALANCE() -> None:
    w = DummyWorld(balances={0x9BBFED6889322E016E0A02EE459D306FC19545D8: 125985})
    assert BALANCE(w, 0x9BBFED6889322E016E0A02EE459D306FC19545D8) == 125985


def test_ORIGIN() -> None:
    s = State(origin=0xBE862AD9ABFE6F22BCB087716C7D89A26051F74C)
    assert ORIGIN(s) == 0xBE862AD9ABFE6F22BCB087716C7D89A26051F74C


def test_CALLER() -> None:
    s = State(caller=0xBE862AD9ABFE6F22BCB087716C7D89A26051F74C)
    assert CALLER(s) == 0xBE862AD9ABFE6F22BCB087716C7D89A26051F74C


def test_CALLVALUE() -> None:
    s = State(callvalue=123456789)
    assert CALLVALUE(s) == 123456789


def test_CALLDATALOAD() -> None:
    s = State(
        calldata=b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
    )
    assert (
        CALLDATALOAD(s, 0)
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        CALLDATALOAD(s, 31)
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert CALLDATALOAD(s, 32) == 0


def test_CALLDATASIZE() -> None:
    s = State(calldata=b"\xff")
    assert CALLDATASIZE(s) == 1


def test_CALLDATACOPY() -> None:
    s = State(
        calldata=b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
    )

    CALLDATACOPY(s, 0, 0, 32)
    assert (
        _dump_memory(s)
        == "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )

    CALLDATACOPY(s, 0, 31, 8)
    assert (
        _dump_memory(s)
        == "0xFF00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )


def test_CODESIZE() -> None:
    s = State(address=0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        }
    )
    assert CODESIZE(s, w) == 32


def test_CODECOPY() -> None:
    s = State(address=0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        }
    )

    CODECOPY(s, w, 0, 0, 32)
    assert (
        _dump_memory(s)
        == "0x7DFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )

    CODECOPY(s, w, 0, 31, 8)
    assert (
        _dump_memory(s)
        == "0x7F00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )


def test_GASPRICE() -> None:
    s = State(gasprice=10)
    assert GASPRICE(s) == 10


def test_EXTCODESIZE() -> None:
    w = DummyWorld(
        codes={
            0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        }
    )
    assert EXTCODESIZE(w, 0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B) == 32


def test_EXTCODECOPY() -> None:
    w = DummyWorld(
        codes={
            0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        }
    )
    s = State()

    EXTCODECOPY(s, w, 0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B, 0, 0, 32)
    assert (
        _dump_memory(s)
        == "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )

    EXTCODECOPY(s, w, 0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B, 0, 31, 8)
    assert (
        _dump_memory(s)
        == "0xFF00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )
