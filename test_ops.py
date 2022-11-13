from typing import Dict

import z3

from common import BW, BY, Address, ByteArray, State, uint256
from ops import *


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
        v += z3.simplify(s.memory[i]).as_long().to_bytes(1, "big").hex()
    return "0x" + v.upper()


def test_STOP() -> None:
    s = State(returndata=b"1234")
    STOP(s)
    assert s.success == True
    assert s.returndata == b""


def test_ADD() -> None:
    assert z3.simplify(ADD(BW(10), BW(10))) == 20
    assert (
        z3.simplify(
            ADD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(1),
            )
        )
        == 0
    )


def test_MUL() -> None:
    assert z3.simplify(MUL(BW(10), BW(10))) == 100
    assert (
        z3.simplify(
            MUL(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                2,
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert z3.simplify(SUB(BW(10), BW(10))) == 0
    assert (
        z3.simplify(SUB(BW(0), BW(1)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert z3.simplify(DIV(BW(10), BW(10))) == 1
    assert z3.simplify(DIV(BW(1), BW(2))) == 0
    assert z3.simplify(DIV(BW(10), BW(0))) == 0


def test_SDIV() -> None:
    assert z3.simplify(SDIV(BW(10), BW(10))) == 1
    assert (
        z3.simplify(
            SDIV(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            )
        )
        == 2
    )
    assert z3.simplify(SDIV(BW(10), BW(0))) == 0


def test_MOD() -> None:
    assert z3.simplify(MOD(BW(10), BW(3))) == 1
    assert z3.simplify(MOD(BW(17), BW(5))) == 2
    assert z3.simplify(MOD(BW(10), BW(0))) == 0


def test_SMOD() -> None:
    assert z3.simplify(SMOD(BW(10), BW(3))) == 1
    assert (
        z3.simplify(
            SMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert z3.simplify(SMOD(BW(10), BW(0))) == 0


def test_ADDMOD() -> None:
    assert z3.simplify(ADDMOD(BW(10), BW(10), BW(8))) == 4
    assert (
        z3.simplify(
            ADDMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(2),
                BW(2),
            )
        )
        == 1
    )


def test_MULMOD() -> None:
    assert z3.simplify(MULMOD(BW(10), BW(10), BW(8))) == 4
    assert (
        z3.simplify(
            MULMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(12),
            )
        )
        == 9
    )


def test_EXP() -> None:
    assert z3.simplify(EXP(BW(10), BW(2))) == 100
    assert z3.simplify(EXP(BW(2), BW(2))) == 4


def test_SIGNEXTEND() -> None:
    assert (
        z3.simplify(SIGNEXTEND(BW(0), BW(0xFF)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        z3.simplify(SIGNEXTEND(BW(0), BW(0xAA)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert z3.simplify(SIGNEXTEND(BW(0), BW(0x7F))) == 0x7F
    assert z3.simplify(SIGNEXTEND(BW(2), BW(0xFF))) == 0xFF
    assert z3.simplify(SIGNEXTEND(BW(0x7F), BW(0x7F))) == 0x7F


def test_LT() -> None:
    assert z3.simplify(LT(BW(8), BW(10))) == 1
    assert z3.simplify(LT(BW(10), BW(10))) == 0


def test_GT() -> None:
    assert z3.simplify(GT(BW(10), BW(8))) == 1
    assert z3.simplify(GT(BW(10), BW(10))) == 0


def test_SLT() -> None:
    assert (
        z3.simplify(
            SLT(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(0),
            )
        )
        == 1
    )
    assert z3.simplify(SLT(BW(10), BW(10))) == 0


def test_SGT() -> None:
    assert (
        z3.simplify(
            SGT(
                BW(0),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            )
        )
        == 1
    )
    assert z3.simplify(SGT(BW(10), BW(10))) == 0


def test_EQ() -> None:
    assert z3.simplify(EQ(BW(10), BW(10))) == 1
    assert z3.simplify(EQ(BW(10), BW(8))) == 0


def test_ISZERO() -> None:
    assert z3.simplify(ISZERO(BW(10))) == 0
    assert z3.simplify(ISZERO(BW(0))) == 1


def test_AND() -> None:
    assert z3.simplify(AND(BW(0x0F), BW(0x0F))) == 0xF
    assert z3.simplify(AND(BW(0xFF), BW(0))) == 0


def test_OR() -> None:
    assert z3.simplify(OR(BW(0xF0), BW(0x0F))) == 0xFF
    assert z3.simplify(OR(BW(0xFF), BW(0xFF))) == 0xFF


def test_XOR() -> None:
    assert z3.simplify(XOR(BW(0xF0), BW(0x0F))) == 0xFF
    assert z3.simplify(XOR(BW(0xFF), BW(0xFF))) == 0


def test_NOT() -> None:
    assert (
        z3.simplify(NOT(BW(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    assert z3.simplify(BYTE(BW(31), BW(0xFF))) == 0xFF
    assert z3.simplify(BYTE(BW(30), BW(0x8800))) == 0x88
    assert z3.simplify(BYTE(BW(30), BW(0xAABBCC))) == 0xBB
    assert z3.simplify(BYTE(BW(123456), BW(0xAABBCC))) == 0


def test_SHL() -> None:
    assert z3.simplify(SHL(BW(1), BW(1))) == 2
    assert (
        z3.simplify(
            SHL(
                BW(4),
                BW(0xFF00000000000000000000000000000000000000000000000000000000000000),
            )
        )
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert z3.simplify(SHR(BW(1), BW(2))) == 1
    assert z3.simplify(SHR(BW(4), BW(0xFF))) == 0xF
    assert z3.simplify(SHR(BW(123), BW(0xAA))) == 0


def test_SAR() -> None:
    assert z3.simplify(SAR(BW(1), BW(2))) == 1
    assert (
        z3.simplify(
            SAR(
                BW(4),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_SHA3() -> None:
    s = State(memory={0: BY(0xFF), 1: BY(0xFF), 2: BY(0xFF), 3: BY(0xFF)})
    assert (
        z3.simplify(SHA3(s, BW(0), BW(4)))
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    s = State(address=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(ADDRESS(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    w = DummyWorld(
        balances={BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8): BW(125985)}
    )
    assert (
        z3.simplify(BALANCE(w, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8)))
        == 125985
    )


def test_ORIGIN() -> None:
    s = State(origin=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(ORIGIN(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    s = State(caller=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(CALLER(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    s = State(callvalue=BW(123456789))
    assert z3.simplify(CALLVALUE(s)) == 123456789


def test_CALLDATALOAD() -> None:
    s = State(
        calldata=ByteArray(
            "CALLDATA",
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        )
    )
    assert (
        z3.simplify(CALLDATALOAD(s, BW(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        z3.simplify(CALLDATALOAD(s, BW(31)))
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert z3.simplify(CALLDATALOAD(s, BW(32))) == 0


def test_CALLDATASIZE() -> None:
    s = State(calldata=ByteArray("CALLDATA", b"\xff"))
    assert CALLDATASIZE(s) == 1


def test_CALLDATACOPY() -> None:
    s = State(
        calldata=ByteArray(
            "CALLDATA",
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        )
    )

    CALLDATACOPY(s, BW(0), BW(0), BW(32))
    assert (
        _dump_memory(s)
        == "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )

    CALLDATACOPY(s, BW(0), BW(31), BW(8))
    assert (
        _dump_memory(s)
        == "0xFF00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )


def test_CODESIZE() -> None:
    s = State(address=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        }
    )
    assert CODESIZE(s, w) == 32


def test_CODECOPY() -> None:
    s = State(address=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        }
    )

    CODECOPY(s, w, BW(0), BW(0), BW(32))
    assert (
        _dump_memory(s)
        == "0x7DFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )

    CODECOPY(s, w, BW(0), BW(31), BW(8))
    assert (
        _dump_memory(s)
        == "0x7F00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )


def test_GASPRICE() -> None:
    s = State(gasprice=BW(10))
    assert z3.simplify(GASPRICE(s)) == 10


def test_EXTCODESIZE() -> None:
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        }
    )
    assert (
        z3.simplify(EXTCODESIZE(w, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8)))
        == 32
    )


def test_EXTCODECOPY() -> None:
    w = DummyWorld(
        codes={
            0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff",
        }
    )
    s = State()

    EXTCODECOPY(
        s, w, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8), BW(0), BW(0), BW(32)
    )
    assert (
        _dump_memory(s)
        == "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )

    EXTCODECOPY(
        s, w, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8), BW(0), BW(31), BW(8)
    )
    assert (
        _dump_memory(s)
        == "0xFF00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
    )


def test_RETURNDATASIZE() -> None:
    s = State(returndata=b"abcdefghijklmnopqrstuvwxyz")
    assert z3.simplify(RETURNDATASIZE(s)) == 26


def test_RETURNDATACOPY() -> None:
    s = State(
        returndata=b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
    )

    RETURNDATACOPY(s, BW(0), BW(0), BW(32))
    assert (
        _dump_memory(s)
        == "0x7DFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )

    RETURNDATACOPY(s, BW(0), BW(31), BW(8))
    assert (
        _dump_memory(s)
        == "0x7F00000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7F"
    )


def test_EXTCODEHASH() -> None:
    # The example on evm.codes is wrong: 0xc5d2... is the hash of the empty
    # string, which shouldn't be possible to observe.
    w = DummyWorld(
        codes={0x9BBFED6889322E016E0A02EE459D306FC19545D8: b"\xff\xff\xff\xff"}
    )
    assert (
        z3.simplify(EXTCODEHASH(w, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8)))
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )
    assert EXTCODEHASH(w, BW(0x123)) == 0


def test_BLOCKHASH() -> None:
    w = DummyWorld(
        blockhashes={
            100000123: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            599423545: 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238,
            599423546: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
            599423547: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        }
    )
    b = Block(number=BW(599423546))
    assert (
        z3.simplify(BLOCKHASH(b, w, BW(599423545)))
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )
    assert z3.simplify(BLOCKHASH(b, w, BW(599423546))) == 0
    assert z3.simplify(BLOCKHASH(b, w, BW(599423547))) == 0


def test_COINBASE() -> None:
    b = Block(coinbase=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(COINBASE(b)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    b = Block(timestamp=BW(1636704767))
    assert z3.simplify(TIMESTAMP(b)) == 1636704767


def test_NUMBER() -> None:
    b = Block(number=BW(1636704767))
    assert z3.simplify(NUMBER(b)) == 1636704767


def test_PREVRANDAO() -> None:
    b = Block(
        prevrandao=BW(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    assert (
        z3.simplify(PREVRANDAO(b))
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    b = Block(gaslimit=BW(0xFFFFFFFFFFFF))
    assert z3.simplify(GASLIMIT(b)) == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    b = Block()
    assert CHAINID(b) == 1


def test_SELFBALANCE() -> None:
    s = State(address=BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    w = DummyWorld(balances={BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8): BW(8)})
    assert z3.simplify(SELFBALANCE(s, w)) == BW(8)


def test_BASEFEE() -> None:
    b = Block(basefee=BW(10))
    assert z3.simplify(BASEFEE(b)) == 10


def test_MLOAD() -> None:
    s = State(memory={31: BY(0xFF)})
    assert z3.simplify(MLOAD(s, 0)) == 0xFF
    assert z3.simplify(MLOAD(s, 1)) == 0xFF00


def test_MSTORE() -> None:
    s = State()
    MSTORE(s, BW(0), BW(0xFF))
    assert (
        _dump_memory(s)
        == "0x00000000000000000000000000000000000000000000000000000000000000FF"
    )
    MSTORE(s, BW(1), BW(0xFF))
    assert (
        _dump_memory(s)
        == "0x0000000000000000000000000000000000000000000000000000000000000000FF"
    )


def test_MSTORE8() -> None:
    s = State()
    MSTORE8(s, BW(0), BW(0xFFFF))
    assert _dump_memory(s) == "0xFF"
    MSTORE8(s, BW(1), BW(0xAABBCCDDEE))
    assert _dump_memory(s) == "0xFFEE"


def test_SLOAD() -> None:
    s = State(storage={0: BW(46)})
    assert z3.simplify(SLOAD(s, BW(0))) == 46
    assert z3.simplify(SLOAD(s, BW(1))) == 0


def test_SSTORE() -> None:
    s = State()

    SSTORE(s, BW(0), BW(0xFFFF))
    assert len(s.storage) == 1
    assert s.storage[0] == 0xFFFF

    SSTORE(s, BW(8965), BW(0xFF))
    assert len(s.storage) == 2
    assert s.storage[0] == 0xFFFF
    assert s.storage[8965] == 0xFF


def test_JUMP() -> None:
    s = State(jumps={8: 90})
    JUMP(s, BW(8))
    assert s.pc == 90


def test_JUMPI() -> None:
    s = State(jumps={8: 90})

    JUMPI(s, BW(8), BW(0))
    assert s.pc == 0

    JUMPI(s, BW(8), BW(1))
    assert s.pc == 90


def test_MSIZE() -> None:
    s = State(memory={123: BY(0x01)})
    assert z3.simplify(MSIZE(s)) == 124


def test_RETURN() -> None:
    s = State(
        returndata=b"1234",
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    RETURN(s, BW(0), BW(2))
    assert s.success == True
    assert s.returndata == b"\xff\x01"


def test_REVERT() -> None:
    s = State(
        returndata=b"1234",
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    REVERT(s, BW(0), BW(2))
    assert s.success == False
    assert s.returndata == b"\xff\x01"


def test_INVALID() -> None:
    s = State(returndata=b"1234")
    INVALID(s)
    assert s.success == False
    assert s.returndata == b""
