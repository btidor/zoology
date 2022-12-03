#!/usr/bin/env pytest

import pytest
import z3

from disassembler import Instruction, Program
from ops import *
from state import State
from symbolic import BA, BW, BY, Bytes, check, concretize_hex
from testlib import make_block, make_contract, make_state


def _dump_memory(s: State) -> str:
    v = ""
    lim = max(s.memory.keys())
    for i in range(lim + 1):
        v += concretize_hex(s.memory[i])
    return "0x" + v.upper()


def test_STOP() -> None:
    s = make_state(returndata=[BW(0x12), BW(0x34)])
    STOP(s)
    assert s.success is True
    assert s.returndata == []


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
                BW(2),
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
    s = make_state(memory={0: BY(0xFF), 1: BY(0xFF), 2: BY(0xFF), 3: BY(0xFF)})
    digest = SHA3(s, BW(0), BW(4))

    solver = z3.Optimize()
    s.sha3.constrain(solver)
    assert check(solver)
    assert (
        solver.model().eval(digest)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    s = make_state(address=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(ADDRESS(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    s = make_state()
    s.universe.balances[BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8)] = BW(125985)
    assert (
        z3.simplify(
            BALANCE(s.universe, s, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
        )
        == 125985
    )


def test_ORIGIN() -> None:
    s = make_state(origin=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(ORIGIN(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    s = make_state(caller=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(CALLER(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    s = make_state(callvalue=BW(123456789))
    assert z3.simplify(CALLVALUE(s)) == 123456789


def test_CALLDATALOAD() -> None:
    s = make_state(
        calldata=Bytes(
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
    s = make_state(calldata=Bytes("CALLDATA", b"\xff"))
    assert CALLDATASIZE(s) == 1


def test_CALLDATACOPY() -> None:
    s = make_state(
        calldata=Bytes(
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


def test_GASPRICE() -> None:
    s = make_state(gasprice=BW(10))
    assert z3.simplify(GASPRICE(s)) == 10


def test_RETURNDATASIZE() -> None:
    s = make_state(
        returndata=[z3.BitVecVal(b, 8) for b in b"abcdefghijklmnopqrstuvwxyz"]
    )
    assert z3.simplify(RETURNDATASIZE(s)) == 26


def test_RETURNDATACOPY() -> None:
    s = make_state(
        returndata=[
            z3.BitVecVal(b, 8)
            for b in b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        ]
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


def test_COINBASE() -> None:
    b = make_block(coinbase=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert z3.simplify(COINBASE(b)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    b = make_block(timestamp=BW(1636704767))
    assert z3.simplify(TIMESTAMP(b)) == 1636704767


def test_NUMBER() -> None:
    b = make_block(number=BW(1636704767))
    assert z3.simplify(NUMBER(b)) == 1636704767


def test_PREVRANDAO() -> None:
    b = make_block(
        prevrandao=BW(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    assert (
        z3.simplify(PREVRANDAO(b))
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    b = make_block(gaslimit=BW(0xFFFFFFFFFFFF))
    assert z3.simplify(GASLIMIT(b)) == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    b = make_block()
    assert CHAINID(b) == 1


def test_BASEFEE() -> None:
    b = make_block(basefee=BW(10))
    assert z3.simplify(BASEFEE(b)) == 10


def test_MLOAD() -> None:
    s = make_state(memory={31: BY(0xFF)})
    assert z3.simplify(MLOAD(s, BW(0))) == 0xFF
    assert z3.simplify(MLOAD(s, BW(1))) == 0xFF00


def test_MSTORE() -> None:
    s = make_state()
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
    s = make_state()
    MSTORE8(s, BW(0), BW(0xFFFF))
    assert _dump_memory(s) == "0xFF"
    MSTORE8(s, BW(1), BW(0xAABBCCDDEE))
    assert _dump_memory(s) == "0xFFEE"


def test_SLOAD() -> None:
    c = make_contract()
    c.storage[BW(0)] = BW(46)
    assert z3.simplify(SLOAD(c, BW(0))) == 46
    assert len(c.storage.accessed) == 1
    assert z3.simplify(c.storage.accessed[0]) == 0


def test_SSTORE() -> None:
    c = make_contract()

    SSTORE(c, BW(0), BW(0xFFFF))
    assert z3.simplify(c.storage[BW(0)]) == 0xFFFF

    SSTORE(c, BW(8965), BW(0xFF))
    assert z3.simplify(c.storage[BW(0)]) == 0xFFFF
    assert z3.simplify(c.storage[BW(8965)]) == 0xFF


def test_JUMP() -> None:
    p = Program(jumps={8: 90})
    s = make_state()
    JUMP(p, s, BW(8))
    assert s.pc == 90
    with pytest.raises(KeyError):
        JUMP(p, s, BW(99))


def test_PC() -> None:
    ins = Instruction(0x12, 1, "PC")
    assert z3.simplify(PC(ins)) == 0x12


def test_MSIZE() -> None:
    s = make_state(memory={123: BY(0x01)})
    assert z3.simplify(MSIZE(s)) == 124


def test_PUSH() -> None:
    ins = Instruction(0x0, 2, "PUSH", 1, BW(0x01))
    assert z3.simplify(PUSH(ins)) == 0x01

    ins = Instruction(0x1, 2, "PUSH", 1)
    with pytest.raises(ValueError):
        PUSH(ins)


def test_DUP() -> None:
    s = make_state(stack=[BW(0x1234)])

    ins = Instruction(0x0, 1, "DUP", 1)
    assert z3.simplify(DUP(ins, s)) == 0x1234

    ins = Instruction(0x0, 1, "DUP")
    with pytest.raises(ValueError):
        DUP(ins, s)


def test_SWAP() -> None:
    s = make_state(stack=[BW(0x1234), BW(0x5678)])

    ins = Instruction(0x0, 1, "SWAP", 1)
    SWAP(ins, s)
    stack = [z3.simplify(x) for x in s.stack]
    assert stack == [0x5678, 0x1234]

    ins = Instruction(0x0, 1, "SWAP")
    with pytest.raises(ValueError):
        SWAP(ins, s)


def test_CALL() -> None:
    s = make_state(returndata=[BY(1)])
    s.universe.balances[s.address] = BW(125)
    res = CALL(s.universe, s, BW(0), BW(0x1234), BW(123), BW(0), BW(0), BW(0), BW(0))
    assert z3.simplify(res) == 1
    assert len(s.returndata) == 0
    assert z3.simplify(s.universe.balances[BA(0x1234)]) == 123
    assert z3.simplify(s.universe.balances[s.address]) == 2


def test_RETURN() -> None:
    s = make_state(
        returndata=[BW(0x12), BW(0x34)],
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    RETURN(s, BW(0), BW(2))
    assert s.success is True
    assert [z3.simplify(b) for b in s.returndata] == [0xFF, 0x01]


def test_REVERT() -> None:
    s = make_state(
        returndata=[BW(0x12), BW(0x34)],
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    REVERT(s, BW(0), BW(2))
    assert s.success is False
    assert [z3.simplify(b) for b in s.returndata] == [0xFF, 0x01]


def test_INVALID() -> None:
    s = make_state(returndata=[BW(0x12), BW(0x34)])
    INVALID(s)
    assert s.success is False
    assert s.returndata == []


def test_SELFDESTRUCT() -> None:
    with pytest.raises(Exception):
        SELFDESTRUCT()
