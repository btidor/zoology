#!/usr/bin/env pytest
# ruff: noqa: F403 F405

import pytest

from bytes import Bytes, Memory
from disassembler import Instruction, disassemble
from ops import *
from smt import Array, Solver, Uint160, Uint256
from state import Block, Contract, Transaction


def test_STOP() -> None:
    s, d = STOP()
    assert s is True
    assert d.reveal() == b""


def test_ADD() -> None:
    assert ADD(Uint256(10), Uint256(10)).reveal() == 20
    assert (
        ADD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(1),
        ).reveal()
        == 0
    )


def test_MUL() -> None:
    assert MUL(Uint256(10), Uint256(10)).reveal() == 100
    assert (
        MUL(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(2),
        ).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert SUB(Uint256(10), Uint256(10)).reveal() == 0
    assert (
        SUB(Uint256(0), Uint256(1)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert DIV(Uint256(10), Uint256(10)).reveal() == 1
    assert DIV(Uint256(1), Uint256(2)).reveal() == 0
    assert DIV(Uint256(10), Uint256(0)).reveal() == 0


def test_SDIV() -> None:
    assert SDIV(Uint256(10), Uint256(10)).reveal() == 1
    assert (
        SDIV(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
        ).reveal()
        == 2
    )
    assert SDIV(Uint256(10), Uint256(0)).reveal() == 0


def test_MOD() -> None:
    assert MOD(Uint256(10), Uint256(3)).reveal() == 1
    assert MOD(Uint256(17), Uint256(5)).reveal() == 2
    assert MOD(Uint256(10), Uint256(0)).reveal() == 0


def test_SMOD() -> None:
    assert SMOD(Uint256(10), Uint256(3)).reveal() == 1
    assert (
        SMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD),
        ).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert SMOD(Uint256(10), Uint256(0)).reveal() == 0


def test_ADDMOD() -> None:
    assert ADDMOD(Uint256(10), Uint256(10), Uint256(8)).reveal() == 4
    assert (
        ADDMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(2),
            Uint256(2),
        ).reveal()
        == 1
    )


def test_MULMOD() -> None:
    assert MULMOD(Uint256(10), Uint256(10), Uint256(8)).reveal() == 4
    assert (
        MULMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(12),
        ).reveal()
        == 9
    )


def test_EXP() -> None:
    assert EXP(Uint256(10), Uint256(2)).reveal() == 100
    assert EXP(Uint256(2), Uint256(2)).reveal() == 4
    assert EXP(Uint256(123), Uint256(0)).reveal() == 1
    assert EXP(Uint256(10), Uint256(18)).reveal() == 10**18


def test_SIGNEXTEND() -> None:
    assert (
        SIGNEXTEND(Uint256(0), Uint256(0xFF)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        SIGNEXTEND(Uint256(0), Uint256(0xAAAA)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert (
        SIGNEXTEND(Uint256(1), Uint256(0xABCD)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFABCD
    )
    assert SIGNEXTEND(Uint256(0), Uint256(0x7F)).reveal() == 0x7F
    assert SIGNEXTEND(Uint256(1), Uint256(0x5BCD)).reveal() == 0x5BCD
    assert SIGNEXTEND(Uint256(2), Uint256(0xFF)).reveal() == 0xFF
    assert SIGNEXTEND(Uint256(2), Uint256(0xABCD)).reveal() == 0xABCD
    assert SIGNEXTEND(Uint256(0x7F), Uint256(0x7F)).reveal() == 0x7F


def test_LT() -> None:
    assert LT(Uint256(8), Uint256(10)).reveal() == 1
    assert LT(Uint256(10), Uint256(10)).reveal() == 0


def test_GT() -> None:
    assert GT(Uint256(10), Uint256(8)).reveal() == 1
    assert GT(Uint256(10), Uint256(10)).reveal() == 0


def test_SLT() -> None:
    assert (
        SLT(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(0),
        ).reveal()
        == 1
    )
    assert SLT(Uint256(10), Uint256(10)).reveal() == 0


def test_SGT() -> None:
    assert (
        SGT(
            Uint256(0),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
        ).reveal()
        == 1
    )
    assert SGT(Uint256(10), Uint256(10)).reveal() == 0


def test_EQ() -> None:
    assert EQ(Uint256(10), Uint256(10)).reveal() == 1
    assert EQ(Uint256(10), Uint256(8)).reveal() == 0


def test_ISZERO() -> None:
    assert ISZERO(Uint256(10)).reveal() == 0
    assert ISZERO(Uint256(0)).reveal() == 1


def test_AND() -> None:
    assert AND(Uint256(0x0F), Uint256(0x0F)).reveal() == 0xF
    assert AND(Uint256(0xFF), Uint256(0)).reveal() == 0


def test_OR() -> None:
    assert OR(Uint256(0xF0), Uint256(0x0F)).reveal() == 0xFF
    assert OR(Uint256(0xFF), Uint256(0xFF)).reveal() == 0xFF


def test_XOR() -> None:
    assert XOR(Uint256(0xF0), Uint256(0x0F)).reveal() == 0xFF
    assert XOR(Uint256(0xFF), Uint256(0xFF)).reveal() == 0


def test_NOT() -> None:
    assert (
        NOT(Uint256(0)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    assert BYTE(Uint256(31), Uint256(0xFF)).reveal() == 0xFF
    assert BYTE(Uint256(30), Uint256(0x8800)).reveal() == 0x88
    assert BYTE(Uint256(30), Uint256(0xAABBCC)).reveal() == 0xBB
    assert BYTE(Uint256(123456), Uint256(0xAABBCC)).reveal() == 0


def test_SHL() -> None:
    assert SHL(Uint256(1), Uint256(1)).reveal() == 2
    assert (
        SHL(
            Uint256(4),
            Uint256(0xFF00000000000000000000000000000000000000000000000000000000000000),
        ).reveal()
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert SHR(Uint256(1), Uint256(2)).reveal() == 1
    assert SHR(Uint256(4), Uint256(0xFF)).reveal() == 0xF
    assert SHR(Uint256(123), Uint256(0xAA)).reveal() == 0


def test_SAR() -> None:
    assert SAR(Uint256(1), Uint256(2)).reveal() == 1
    assert (
        SAR(
            Uint256(4),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0),
        ).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_KECCAK256() -> None:
    s = Runtime(memory=Memory(b"\xff\xff\xff\xff"))
    digest = KECCAK256(s, Uint256(0), Uint256(4))

    solver = Solver()
    solver.add(s.path.constraint)
    assert solver.check()
    assert (
        solver.evaluate(digest)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    tx = Transaction(
        address=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8),
    )
    assert ADDRESS(tx).reveal() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    k = Blockchain()
    k.balances[Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)] = Uint256(125985)
    assert (
        BALANCE(k, Uint256(0x9BBFED6889322E016E0A02EE459D306FC19545D8)).reveal()
        == 125985
    )


def test_ORIGIN() -> None:
    tx = Transaction(
        origin=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8),
    )
    assert ORIGIN(tx).reveal() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    tx = Transaction(
        caller=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8),
    )
    assert CALLER(tx).reveal() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    tx = Transaction(callvalue=Uint256(123456789))
    assert CALLVALUE(tx).reveal() == 123456789


def test_CALLDATALOAD() -> None:
    tx = Transaction(
        calldata=Bytes(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    assert (
        CALLDATALOAD(tx, Uint256(0)).reveal()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        CALLDATALOAD(tx, Uint256(31)).reveal()
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert CALLDATALOAD(tx, Uint256(32)).reveal() == 0


def test_CALLDATASIZE() -> None:
    tx = Transaction(calldata=Bytes(b"\xff"))
    assert CALLDATASIZE(tx).reveal() == 1


def test_CALLDATACOPY() -> None:
    tx = Transaction(
        calldata=Bytes(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    r = Runtime()

    CALLDATACOPY(r, tx, Uint256(0), Uint256(0), Uint256(32))
    assert r.memory.reveal() == bytes.fromhex(
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    )

    CALLDATACOPY(r, tx, Uint256(0), Uint256(31), Uint256(8))
    assert r.memory.reveal() == bytes.fromhex(
        "ff00000000000000ffffffffffffffffffffffffffffffffffffffffffffffff"
    )


def test_CODESIZE() -> None:
    r = Runtime(
        program=disassemble(Bytes.fromhex("66000000000000005B")),
    )
    assert CODESIZE(r).reveal() == 9


def test_CODECOPY() -> None:
    r = Runtime(
        program=disassemble(Bytes.fromhex("66000000000000005B")),
    )

    CODECOPY(r, Uint256(0), Uint256(0), Uint256(0x09))
    assert r.memory.reveal() == bytes.fromhex("66000000000000005b")

    CODECOPY(r, Uint256(1), Uint256(8), Uint256(0x20))
    assert r.memory.reveal() == bytes.fromhex(
        "665b00000000000000000000000000000000000000000000000000000000000000"
    )


def test_GASPRICE() -> None:
    tx = Transaction(gasprice=Uint256(10))
    assert GASPRICE(tx).reveal() == 10


def test_EXTCODESIZE() -> None:
    k = Blockchain()
    address = Address(0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD)
    k.contracts[address] = Contract(
        program=disassemble(Bytes.fromhex("66000000000000005B")),
    )
    assert EXTCODESIZE(k, Uint256(address)).reveal() == 9
    assert EXTCODESIZE(k, Uint256(0x1234)).reveal() == 0


def test_EXTCODECOPY() -> None:
    k = Blockchain()
    address = Address(0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD)
    k.contracts[address] = Contract(
        program=disassemble(Bytes.fromhex("66000000000000005B")),
    )
    r = Runtime()
    EXTCODECOPY(k, r, Uint256(address), Uint256(3), Uint256(5), Uint256(7))
    assert r.memory.reveal() == bytes.fromhex("0000000000005b000000")

    EXTCODECOPY(k, r, Uint256(0x1234), Uint256(0), Uint256(0), Uint256(10))
    assert r.memory.reveal() == bytes.fromhex("00000000000000000000")


def test_RETURNDATASIZE() -> None:
    r = Runtime(
        latest_return=Bytes(b"abcdefghijklmnopqrstuvwxyz"),
    )
    assert RETURNDATASIZE(r).reveal() == 26


def test_RETURNDATACOPY() -> None:
    r = Runtime(
        latest_return=Bytes(
            b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        )
    )

    RETURNDATACOPY(r, Uint256(0), Uint256(0), Uint256(32))
    assert r.memory.reveal() == bytes.fromhex(
        "7dffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"
    )

    RETURNDATACOPY(r, Uint256(0), Uint256(31), Uint256(8))
    assert r.memory.reveal() == bytes.fromhex(
        "7f00000000000000ffffffffffffffffffffffffffffffffffffffffffffff7f"
    )


def test_EXTCODEHASH() -> None:
    k = Blockchain()
    address = Address(0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD)
    k.contracts[address] = Contract(
        program=disassemble(Bytes.fromhex("66000000000000005B")),
    )
    r = Runtime()

    assert (
        EXTCODEHASH(k, r, Uint256(address)).reveal()
        == 0xD579742AEE22A336CAC42EFE05B2CF1281DB892E213257B929C2338EA0675B00
    )
    with pytest.raises(NotImplementedError):
        EXTCODEHASH(k, r, Uint256(0x1234))


def test_BLOCKHASH() -> None:
    blk = Block(hashes=Array[Uint8, Uint256](Uint256(0x9999)))
    assert BLOCKHASH(blk, blk.number - Uint256(10)).reveal() == 0x9999
    assert BLOCKHASH(blk, blk.number - Uint256(256)).reveal() == 0x9999
    assert BLOCKHASH(blk, blk.number - Uint256(257)).reveal() == 0
    assert BLOCKHASH(blk, blk.number).reveal() == 0
    assert BLOCKHASH(blk, blk.number + Uint256(10)).reveal() == 0


def test_COINBASE() -> None:
    blk = Block(coinbase=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    assert COINBASE(blk).reveal() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    blk = Block(timestamp=Uint256(1636704767))
    assert TIMESTAMP(blk).reveal() == 1636704767


def test_NUMBER() -> None:
    blk = Block(number=Uint256(1636704767))
    assert NUMBER(blk).reveal() == 1636704767


def test_PREVRANDAO() -> None:
    blk = Block(
        prevrandao=Uint256(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    assert (
        PREVRANDAO(blk).reveal()
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    blk = Block(gaslimit=Uint256(0xFFFFFFFFFFFF))
    assert GASLIMIT(blk).reveal() == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    blk = Block()
    assert CHAINID(blk).reveal() == 1


def test_SELFBALANCE() -> None:
    raise NotImplementedError


def test_BASEFEE() -> None:
    blk = Block(basefee=Uint256(10))
    assert BASEFEE(blk).reveal() == 10


def test_POP() -> None:
    POP(Uint256(0))


def test_MLOAD() -> None:
    r = Runtime(
        memory=Memory(
            bytes.fromhex(
                "00000000000000000000000000000000000000000000000000000000000000FF"
            )
        )
    )
    assert MLOAD(r, Uint256(0)).reveal() == 0xFF
    assert MLOAD(r, Uint256(1)).reveal() == 0xFF00


def test_MSTORE() -> None:
    r = Runtime()
    MSTORE(r, Uint256(0), Uint256(0xFF))
    assert r.memory.reveal() == bytes.fromhex(
        "00000000000000000000000000000000000000000000000000000000000000ff"
    )
    MSTORE(r, Uint256(1), Uint256(0xFF))
    assert r.memory.reveal() == bytes.fromhex(
        "0000000000000000000000000000000000000000000000000000000000000000ff"
    )


def test_MSTORE8() -> None:
    r = Runtime()
    MSTORE8(r, Uint256(0), Uint256(0xFFFF))

    assert r.memory.reveal() == b"\xff"
    MSTORE8(r, Uint256(1), Uint256(0xAABBCCDDEE))
    assert r.memory.reveal() == b"\xff\xee"


def test_SLOAD() -> None:
    r = Runtime()
    r.storage[Uint256(0)] = Uint256(46)
    assert SLOAD(r, Uint256(0)).reveal() == 46


def test_SSTORE() -> None:
    r = Runtime()

    SSTORE(r, Uint256(0), Uint256(0xFFFF))
    assert r.storage[Uint256(0)].reveal() == 0xFFFF

    SSTORE(r, Uint256(8965), Uint256(0xFF))
    assert r.storage[Uint256(0)].reveal() == 0xFFFF
    assert r.storage[Uint256(8965)].reveal() == 0xFF


def test_JUMP() -> None:
    r = Runtime(program=disassemble(Bytes.fromhex("66000000000000005B")))

    JUMP(r, Uint256(8))
    assert r.pc == 1

    with pytest.raises(KeyError):
        JUMP(r, Uint256(99))


def test_JUMPI() -> None:
    raise NotImplementedError


def test_PC() -> None:
    ins = Instruction(0x12, 1, "PC")
    assert PC(ins).reveal() == 0x12


def test_MSIZE() -> None:
    r = Runtime(memory=Memory(b"\x00" * 123 + b"\x01"))
    assert MSIZE(r).reveal() == 124


def test_GAS() -> None:
    raise NotImplementedError


def test_JUMPDEST() -> None:
    JUMPDEST()


def test_PUSH() -> None:
    ins = Instruction(0x0, 2, "PUSH", 1, Uint256(0x01))
    assert PUSH(ins).reveal() == 0x01

    ins = Instruction(0x1, 2, "PUSH", 1)
    with pytest.raises(ValueError):
        PUSH(ins)


def test_DUP() -> None:
    r = Runtime(stack=[Uint256(0x1234)])

    ins = Instruction(0x0, 1, "DUP", 1)
    assert DUP(ins, r).reveal() == 0x1234

    ins = Instruction(0x0, 1, "DUP")
    with pytest.raises(ValueError):
        DUP(ins, r)


def test_SWAP() -> None:
    r = Runtime(stack=[Uint256(0x1234), Uint256(0x5678)])

    ins = Instruction(0x0, 1, "SWAP", 1)
    SWAP(ins, r)
    stack = [x.reveal() for x in r.stack]
    assert stack == [0x5678, 0x1234]

    ins = Instruction(0x0, 1, "SWAP")
    with pytest.raises(ValueError):
        SWAP(ins, r)


def test_LOG() -> None:
    r = Runtime(
        stack=[Uint256(0xABCD)],
        memory=Memory(b"\x12\x34"),
    )
    ins = Instruction(0x0, 1, "LOG", 1)
    LOG(ins, r, Uint256(1), Uint256(1))


def test_CREATE() -> None:
    raise NotImplementedError


def test_CALL() -> None:
    raise NotImplementedError


def test_CALLCODE() -> None:
    raise NotImplementedError


def test_RETURN() -> None:
    r = Runtime(
        memory=Memory(b"\xff\x01"),
        latest_return=Bytes(b"\x12\x34"),
    )
    s, d = RETURN(r, Uint256(0), Uint256(2))
    assert s is True
    assert d.reveal() == b"\xff\x01"


def test_DELEGATECALL() -> None:
    raise NotImplementedError


def test_CREATE2() -> None:
    raise NotImplementedError


def test_STATICCALL() -> None:
    raise NotImplementedError


def test_REVERT() -> None:
    r = Runtime(
        memory=Memory(b"\xff\x01"),
        latest_return=Bytes(b"\x12\x34"),
    )
    s, d = REVERT(r, Uint256(0), Uint256(2))
    assert s is False
    assert d.reveal() == b"\xff\x01"


def test_INVALID() -> None:
    r = Runtime(
        latest_return=Bytes(b"\x12\x34"),
    )
    s, d = INVALID(r)
    assert s is False
    assert d.reveal() == b""


def test_SELFDESTRUCT() -> None:
    raise NotImplementedError
