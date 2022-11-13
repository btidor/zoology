from typing import Dict

import z3

from common import Address, State, uint256
from ops import *

BV00 = z3.BitVecVal(0, 256)
BV01 = z3.BitVecVal(1, 256)
BV02 = z3.BitVecVal(2, 256)
BV04 = z3.BitVecVal(4, 256)
BV08 = z3.BitVecVal(8, 256)
BV10 = z3.BitVecVal(10, 256)
BV0F = z3.BitVecVal(0x0F, 256)
BVF0 = z3.BitVecVal(0xF0, 256)
BVFF = z3.BitVecVal(0xFF, 256)
BVXE = z3.BitVecVal(
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE, 256
)
BVXF = z3.BitVecVal(
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF, 256
)


class DummyWorld(World):
    def __init__(
        self,
        balances: Dict[Address, uint256] = {},
        codes: Dict[Address, bytes] = {},
        blockhashes: Dict[uint256, uint256] = {},
    ):
        self.balances = balances
        self.codes = codes
        self.blockhashes = blockhashes

    def balance(self, address: Address) -> uint256:
        return self.balances.get(address, 0)

    def code(self, address: Address) -> bytes:
        return self.codes.get(address, b"")

    def blockhash(self, blockNumber: uint256) -> uint256:
        return self.blockhashes.get(blockNumber, 0)


def _dump_memory(s: State) -> str:
    v = ""
    lim = max(s.memory.keys())
    for i in range(lim + 1):
        v += s.memory[i].to_bytes(1, "big").hex()
    return "0x" + v.upper()


def test_STOP() -> None:
    s = State(returndata=b"1234")
    STOP(s)
    assert s.success == True
    assert s.returndata == b""


def test_ADD() -> None:
    assert z3.simplify(ADD(BV10, BV10)) == 20
    assert z3.simplify(ADD(BVXF, BV01)) == 0


def test_MUL() -> None:
    assert z3.simplify(MUL(BV10, BV10)) == 100
    assert (
        z3.simplify(MUL(BVXF, 2))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert z3.simplify(SUB(BV10, BV10)) == 0
    assert (
        z3.simplify(SUB(BV00, BV01))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert z3.simplify(DIV(BV10, BV10)) == 1
    assert z3.simplify(DIV(BV01, BV02)) == 0
    assert z3.simplify(DIV(BV10, BV00)) == 0


def test_SDIV() -> None:
    assert z3.simplify(SDIV(BV10, BV10)) == 1
    assert z3.simplify(SDIV(BVXE, BVXF)) == 2
    assert z3.simplify(SDIV(BV10, BV00)) == 0


def test_MOD() -> None:
    assert z3.simplify(MOD(z3.BitVecVal(10, 256), z3.BitVecVal(3, 256))) == 1
    assert z3.simplify(MOD(z3.BitVecVal(17, 256), z3.BitVecVal(5, 256))) == 2
    assert z3.simplify(MOD(z3.BitVecVal(10, 256), z3.BitVecVal(0, 256))) == 0


def test_SMOD() -> None:
    BV03 = z3.BitVecVal(3, 256)
    BVX8 = z3.BitVecVal(
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8, 256
    )
    BVXD = z3.BitVecVal(
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD, 256
    )
    assert z3.simplify(SMOD(BV10, BV03)) == 1
    assert (
        z3.simplify(SMOD(BVX8, BVXD))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert z3.simplify(SMOD(BV10, BV00)) == 0


def test_ADDMOD() -> None:
    assert z3.simplify(ADDMOD(BV10, BV10, BV08)) == 4
    assert z3.simplify(ADDMOD(BVXF, BV02, BV02)) == 1


def test_MULMOD() -> None:
    BV12 = z3.BitVecVal(12, 256)
    assert z3.simplify(MULMOD(BV10, BV10, BV08)) == 4
    assert z3.simplify(MULMOD(BVXF, BVXF, BV12)) == 9


def test_EXP() -> None:
    assert z3.simplify(EXP(BV10, BV02)) == 100
    assert z3.simplify(EXP(BV02, BV02)) == 4


def test_SIGNEXTEND() -> None:
    BVAA = z3.BitVecVal(0xAA, 256)
    BV7F = z3.BitVecVal(0x7F, 256)
    assert (
        z3.simplify(SIGNEXTEND(BV00, BVFF))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        z3.simplify(SIGNEXTEND(BV00, BVAA))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert z3.simplify(SIGNEXTEND(BV00, BV7F)) == 0x7F
    assert z3.simplify(SIGNEXTEND(BV02, BVFF)) == 0xFF
    assert z3.simplify(SIGNEXTEND(BV7F, BV7F)) == 0x7F


def test_LT() -> None:
    assert z3.simplify(LT(BV08, BV10)) == 1
    assert z3.simplify(LT(BV10, BV10)) == 0


def test_GT() -> None:
    assert z3.simplify(GT(BV10, BV08)) == 1
    assert z3.simplify(GT(BV10, BV10)) == 0


def test_SLT() -> None:
    assert z3.simplify(SLT(BVXF, BV00)) == 1
    assert z3.simplify(SLT(BV10, BV10)) == 0


def test_SGT() -> None:
    assert z3.simplify(SGT(BV00, BVXF)) == 1
    assert z3.simplify(SGT(BV10, BV10)) == 0


def test_EQ() -> None:
    assert z3.simplify(EQ(BV10, BV10)) == 1
    assert z3.simplify(EQ(BV10, BV08)) == 0


def test_ISZERO() -> None:
    assert z3.simplify(ISZERO(BV10)) == 0
    assert z3.simplify(ISZERO(BV00)) == 1


def test_AND() -> None:
    assert z3.simplify(AND(BV0F, BV0F)) == 0xF
    assert z3.simplify(AND(BVFF, BV00)) == 0


def test_OR() -> None:
    assert z3.simplify(OR(BVF0, BV0F)) == 0xFF
    assert z3.simplify(OR(BVFF, BVFF)) == 0xFF


def test_XOR() -> None:
    assert z3.simplify(XOR(BVF0, BV0F)) == 0xFF
    assert z3.simplify(XOR(BVFF, BVFF)) == 0


def test_NOT() -> None:
    assert (
        z3.simplify(NOT(BV00))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    BV30 = z3.BitVecVal(30, 256)
    BV31 = z3.BitVecVal(31, 256)
    BV123456 = z3.BitVecVal(123456, 256)
    assert z3.simplify(BYTE(BV31, z3.BitVecVal(0xFF, 256))) == 0xFF
    assert z3.simplify(BYTE(BV30, z3.BitVecVal(0x8800, 256))) == 0x88
    assert z3.simplify(BYTE(BV30, z3.BitVecVal(0xAABBCC, 256))) == 0xBB
    assert z3.simplify(BYTE(BV123456, z3.BitVecVal(0xAABBCC, 256))) == 0


def test_SHL() -> None:
    BVZ2 = z3.BitVecVal(
        0xFF00000000000000000000000000000000000000000000000000000000000000, 256
    )
    assert z3.simplify(SHL(BV01, BV01)) == 2
    assert (
        z3.simplify(SHL(BV04, BVZ2))
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    BV123 = z3.BitVecVal(123, 256)
    BVAA = z3.BitVecVal(0xAA, 256)
    assert z3.simplify(SHR(BV01, BV02)) == 1
    assert z3.simplify(SHR(BV04, BVFF)) == 0xF
    assert z3.simplify(SHR(BV123, BVAA)) == 0


def test_SAR() -> None:
    BVZ = z3.BitVecVal(
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0, 256
    )
    assert z3.simplify(SAR(BV01, BV02)) == 1
    assert (
        z3.simplify(SAR(BV04, BVZ))
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


def test_RETURNDATASIZE() -> None:
    s = State(returndata=b"abcdefghijklmnopqrstuvwxyz")
    assert RETURNDATASIZE(s) == 26


def test_RETURNDATACOPY() -> None:
    s = State(
        returndata=b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
    )

    RETURNDATACOPY(s, 0, 0, 32)
    assert (
        _dump_memory(s)
        == "0x7DFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )

    RETURNDATACOPY(s, 0, 31, 8)
    assert (
        _dump_memory(s)
        == "0x7F00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )


def test_EXTCODEHASH() -> None:
    # The example on evm.codes is wrong: 0xc5d2... is the hash of the empty
    # string, which shouldn't be possible to observe.
    w = DummyWorld(
        codes={0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B: b"\xff\xff\xff\xff"}
    )
    assert (
        EXTCODEHASH(w, 0x43A61F3F4C73EA0D444C5C1C1A8544067A86219B)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )
    assert EXTCODEHASH(w, 0x123) == 0


def test_BLOCKHASH() -> None:
    w = DummyWorld(
        blockhashes={
            100000123: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            599423545: 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238,
            599423546: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            599423547: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        }
    )
    b = Block(number=599423546)
    assert BLOCKHASH(b, w, 100000123) == 0
    assert (
        BLOCKHASH(b, w, 599423545)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )
    assert BLOCKHASH(b, w, 599423546) == 0
    assert BLOCKHASH(b, w, 599423547) == 0


def test_COINBASE() -> None:
    b = Block(coinbase=0x5B38DA6A701C568545DCFCB03FCB875F56BEDDC4)
    assert COINBASE(b) == 0x5B38DA6A701C568545DCFCB03FCB875F56BEDDC4


def test_TIMESTAMP() -> None:
    b = Block(timestamp=1636704767)
    assert TIMESTAMP(b) == 1636704767


def test_NUMBER() -> None:
    b = Block(number=1636704767)
    assert NUMBER(b) == 1636704767


def test_PREVRANDAO() -> None:
    b = Block(
        prevrandao=0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )
    assert (
        PREVRANDAO(b)
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    b = Block(gaslimit=0xFFFFFFFFFFFF)
    assert GASLIMIT(b) == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    b = Block()
    assert CHAINID(b) == 1


def test_SELFBALANCE() -> None:
    s = State(address=0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    w = DummyWorld(balances={0x9BBFED6889322E016E0A02EE459D306FC19545D8: 9})
    assert SELFBALANCE(s, w) == 9


def test_BASEFEE() -> None:
    b = Block(basefee=10)
    assert BASEFEE(b) == 10


def test_MLOAD() -> None:
    s = State(memory={31: 0xFF})
    assert MLOAD(s, 0) == 0xFF
    assert MLOAD(s, 1) == 0xFF00


def test_MSTORE() -> None:
    s = State()
    MSTORE(s, 0, 0xFF)
    assert (
        _dump_memory(s)
        == "0x00000000000000000000000000000000000000000000000000000000000000FF"
    )
    MSTORE(s, 1, 0xFF)
    assert (
        _dump_memory(s)
        == "0x0000000000000000000000000000000000000000000000000000000000000000FF"
    )


def test_MSTORE8() -> None:
    s = State()
    MSTORE8(s, 0, 0xFFFF)
    assert _dump_memory(s) == "0xFF"
    MSTORE8(s, 1, 0xAABBCCDDEE)
    assert _dump_memory(s) == "0xFFEE"


def test_SLOAD() -> None:
    s = State(storage={0: 46})
    assert SLOAD(s, 0) == 46
    assert SLOAD(s, 1) == 0


def test_SSTORE() -> None:
    s = State()

    SSTORE(s, 0, 0xFFFF)
    assert len(s.storage) == 1
    assert s.storage[0] == 0xFFFF

    SSTORE(s, 8965, 0xFF)
    assert len(s.storage) == 2
    assert s.storage[0] == 0xFFFF
    assert s.storage[8965] == 0xFF


def test_JUMP() -> None:
    s = State(jumps={12: 34})
    JUMP(s, 12)
    assert s.pc == 34


def test_JUMPI() -> None:
    s = State(jumps={12: 34})

    JUMPI(s, 12, 0)
    assert s.pc == 0

    JUMPI(s, 12, 1)
    assert s.pc == 34


def test_MSIZE() -> None:
    s = State(memory={123: 1})
    assert MSIZE(s) == 124


def test_RETURN() -> None:
    s = State(
        returndata=b"1234",
        memory={0: 0xFF, 1: 0x01},
    )
    RETURN(s, 0, 2)
    assert s.success == True
    assert s.returndata == b"\xff\x01"


def test_REVERT() -> None:
    s = State(
        returndata=b"1234",
        memory={0: 0xFF, 1: 0x01},
    )
    REVERT(s, 0, 2)
    assert s.success == False
    assert s.returndata == b"\xff\x01"


def test_INVALID() -> None:
    s = State(returndata=b"1234")
    INVALID(s)
    assert s.success == False
    assert s.returndata == b""
