#!/usr/bin/env pytest

import pytest

from disassembler import Instruction, disassemble
from environment import Block
from ops import *
from smt.arrays import Array
from smt.bytes import FrozenBytes, MutableBytes
from smt.smt import Uint160, Uint256
from smt.solver import Solver
from state import Termination

from .helpers import concretize


def test_STOP() -> None:
    s = State(latest_return=FrozenBytes.concrete(b"\x12\x34"))
    STOP(s)
    assert isinstance(s.pc, Termination)
    assert s.pc.success is True
    assert s.pc.returndata.unwrap() == b""


def test_ADD() -> None:
    assert concretize(ADD(Uint256(10), Uint256(10))) == 20
    assert (
        concretize(
            ADD(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(1),
            )
        )
        == 0
    )


def test_MUL() -> None:
    assert concretize(MUL(Uint256(10), Uint256(10))) == 100
    assert (
        concretize(
            MUL(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(2),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert concretize(SUB(Uint256(10), Uint256(10))) == 0
    assert (
        concretize(SUB(Uint256(0), Uint256(1)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert concretize(DIV(Uint256(10), Uint256(10))) == 1
    assert concretize(DIV(Uint256(1), Uint256(2))) == 0
    assert concretize(DIV(Uint256(10), Uint256(0))) == 0


def test_SDIV() -> None:
    assert concretize(SDIV(Uint256(10), Uint256(10))) == 1
    assert (
        concretize(
            SDIV(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
                ),
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
            )
        )
        == 2
    )
    assert concretize(SDIV(Uint256(10), Uint256(0))) == 0


def test_MOD() -> None:
    assert concretize(MOD(Uint256(10), Uint256(3))) == 1
    assert concretize(MOD(Uint256(17), Uint256(5))) == 2
    assert concretize(MOD(Uint256(10), Uint256(0))) == 0


def test_SMOD() -> None:
    assert concretize(SMOD(Uint256(10), Uint256(3))) == 1
    assert (
        concretize(
            SMOD(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8
                ),
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD
                ),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert concretize(SMOD(Uint256(10), Uint256(0))) == 0


def test_ADDMOD() -> None:
    assert concretize(ADDMOD(Uint256(10), Uint256(10), Uint256(8))) == 4
    assert (
        concretize(
            ADDMOD(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(2),
                Uint256(2),
            )
        )
        == 1
    )


def test_MULMOD() -> None:
    assert concretize(MULMOD(Uint256(10), Uint256(10), Uint256(8))) == 4
    assert (
        concretize(
            MULMOD(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(12),
            )
        )
        == 9
    )


def test_EXP() -> None:
    assert concretize(EXP(Uint256(10), Uint256(2))) == 100
    assert concretize(EXP(Uint256(2), Uint256(2))) == 4


def test_SIGNEXTEND() -> None:
    assert (
        concretize(SIGNEXTEND(Uint256(0), Uint256(0xFF)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        concretize(SIGNEXTEND(Uint256(0), Uint256(0xAAAA)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert (
        concretize(SIGNEXTEND(Uint256(1), Uint256(0xABCD)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFABCD
    )
    assert concretize(SIGNEXTEND(Uint256(0), Uint256(0x7F))) == 0x7F
    assert concretize(SIGNEXTEND(Uint256(1), Uint256(0x5BCD))) == 0x5BCD
    assert concretize(SIGNEXTEND(Uint256(2), Uint256(0xFF))) == 0xFF
    assert concretize(SIGNEXTEND(Uint256(2), Uint256(0xABCD))) == 0xABCD
    assert concretize(SIGNEXTEND(Uint256(0x7F), Uint256(0x7F))) == 0x7F


def test_LT() -> None:
    assert concretize(LT(Uint256(8), Uint256(10))) == 1
    assert concretize(LT(Uint256(10), Uint256(10))) == 0


def test_GT() -> None:
    assert concretize(GT(Uint256(10), Uint256(8))) == 1
    assert concretize(GT(Uint256(10), Uint256(10))) == 0


def test_SLT() -> None:
    assert (
        concretize(
            SLT(
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
                Uint256(0),
            )
        )
        == 1
    )
    assert concretize(SLT(Uint256(10), Uint256(10))) == 0


def test_SGT() -> None:
    assert (
        concretize(
            SGT(
                Uint256(0),
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                ),
            )
        )
        == 1
    )
    assert concretize(SGT(Uint256(10), Uint256(10))) == 0


def test_EQ() -> None:
    assert concretize(EQ(Uint256(10), Uint256(10))) == 1
    assert concretize(EQ(Uint256(10), Uint256(8))) == 0


def test_ISZERO() -> None:
    assert concretize(ISZERO(Uint256(10))) == 0
    assert concretize(ISZERO(Uint256(0))) == 1


def test_AND() -> None:
    assert concretize(AND(Uint256(0x0F), Uint256(0x0F))) == 0xF
    assert concretize(AND(Uint256(0xFF), Uint256(0))) == 0


def test_OR() -> None:
    assert concretize(OR(Uint256(0xF0), Uint256(0x0F))) == 0xFF
    assert concretize(OR(Uint256(0xFF), Uint256(0xFF))) == 0xFF


def test_XOR() -> None:
    assert concretize(XOR(Uint256(0xF0), Uint256(0x0F))) == 0xFF
    assert concretize(XOR(Uint256(0xFF), Uint256(0xFF))) == 0


def test_NOT() -> None:
    assert (
        concretize(NOT(Uint256(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    assert concretize(BYTE(Uint256(31), Uint256(0xFF))) == 0xFF
    assert concretize(BYTE(Uint256(30), Uint256(0x8800))) == 0x88
    assert concretize(BYTE(Uint256(30), Uint256(0xAABBCC))) == 0xBB
    assert concretize(BYTE(Uint256(123456), Uint256(0xAABBCC))) == 0


def test_SHL() -> None:
    assert concretize(SHL(Uint256(1), Uint256(1))) == 2
    assert (
        concretize(
            SHL(
                Uint256(4),
                Uint256(
                    0xFF00000000000000000000000000000000000000000000000000000000000000
                ),
            )
        )
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert concretize(SHR(Uint256(1), Uint256(2))) == 1
    assert concretize(SHR(Uint256(4), Uint256(0xFF))) == 0xF
    assert concretize(SHR(Uint256(123), Uint256(0xAA))) == 0


def test_SAR() -> None:
    assert concretize(SAR(Uint256(1), Uint256(2))) == 1
    assert (
        concretize(
            SAR(
                Uint256(4),
                Uint256(
                    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0
                ),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_SHA3() -> None:
    s = State(memory=MutableBytes.concrete(b"\xff\xff\xff\xff"))
    digest = SHA3(s, Uint256(0), Uint256(4))

    solver = Solver()
    s.sha3.constrain(solver)
    assert solver.check()
    assert (
        concretize(solver.evaluate(digest))
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    contract = Contract(address=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = State(contract=contract)
    assert concretize(ADDRESS(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    s = State()
    s.universe.balances[Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)] = Uint256(
        125985
    )
    assert (
        concretize(BALANCE(s, Uint256(0x9BBFED6889322E016E0A02EE459D306FC19545D8)))
        == 125985
    )


def test_ORIGIN() -> None:
    transaction = Transaction(
        origin=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = State(transaction=transaction)
    assert concretize(ORIGIN(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    transaction = Transaction(
        caller=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = State(transaction=transaction)
    assert concretize(CALLER(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    transaction = Transaction(callvalue=Uint256(123456789))
    s = State(transaction=transaction)
    assert concretize(CALLVALUE(s)) == 123456789


def test_CALLDATALOAD() -> None:
    transaction = Transaction(
        calldata=FrozenBytes.concrete(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    s = State(transaction=transaction)
    assert (
        concretize(CALLDATALOAD(s, Uint256(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        concretize(CALLDATALOAD(s, Uint256(31)))
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert concretize(CALLDATALOAD(s, Uint256(32))) == 0


def test_CALLDATASIZE() -> None:
    transaction = Transaction(calldata=FrozenBytes.concrete(b"\xff"))
    s = State(transaction=transaction)
    assert concretize(CALLDATASIZE(s)) == 1


def test_CALLDATACOPY() -> None:
    transaction = Transaction(
        calldata=FrozenBytes.concrete(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    s = State(transaction=transaction)

    CALLDATACOPY(s, Uint256(0), Uint256(0), Uint256(32))
    assert (
        s.memory.unwrap().hex()
        == "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
    )

    CALLDATACOPY(s, Uint256(0), Uint256(31), Uint256(8))
    assert (
        s.memory.unwrap().hex()
        == "ff00000000000000ffffffffffffffffffffffffffffffffffffffffffffffff"
    )


def test_CODESIZE() -> None:
    s = State(
        contract=Contract(
            program=disassemble(bytes.fromhex("66000000000000005B")),
        )
    )
    assert concretize(CODESIZE(s)) == 9


def test_CODECOPY() -> None:
    s = State(
        contract=Contract(
            program=disassemble(bytes.fromhex("66000000000000005B")),
        )
    )

    CODECOPY(s, Uint256(0), Uint256(0), Uint256(0x09))
    assert s.memory.unwrap().hex() == "66000000000000005b"

    CODECOPY(s, Uint256(1), Uint256(8), Uint256(0x20))
    assert (
        s.memory.unwrap().hex()
        == "665b00000000000000000000000000000000000000000000000000000000000000"
    )


def test_GASPRICE() -> None:
    transaction = Transaction(gasprice=Uint256(10))
    s = State(transaction=transaction)
    assert concretize(GASPRICE(s)) == 10


def test_EXTCODESIZE() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = Contract(
        address=Uint160(address),
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    s = State()
    s.universe.add_contract(contract)
    assert concretize(EXTCODESIZE(s, Uint256(address))) == 9
    assert concretize(EXTCODESIZE(s, Uint256(0x1234))) == 0


def test_EXTCODECOPY() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = Contract(
        address=Uint160(address),
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    s = State()
    s.universe.add_contract(contract)

    EXTCODECOPY(s, Uint256(address), Uint256(3), Uint256(5), Uint256(7))
    assert s.memory.unwrap().hex() == "0000000000005b000000"

    EXTCODECOPY(s, Uint256(0x1234), Uint256(0), Uint256(0), Uint256(10))
    assert s.memory.unwrap().hex() == "00000000000000000000"


def test_RETURNDATASIZE() -> None:
    s = State(latest_return=FrozenBytes.concrete(b"abcdefghijklmnopqrstuvwxyz"))
    assert concretize(RETURNDATASIZE(s)) == 26


def test_RETURNDATACOPY() -> None:
    s = State(
        latest_return=FrozenBytes.concrete(
            b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        )
    )

    RETURNDATACOPY(s, Uint256(0), Uint256(0), Uint256(32))
    assert (
        s.memory.unwrap().hex()
        == "7dffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f"
    )

    RETURNDATACOPY(s, Uint256(0), Uint256(31), Uint256(8))
    assert (
        s.memory.unwrap().hex()
        == "7f00000000000000ffffffffffffffffffffffffffffffffffffffffffffff7f"
    )


def test_EXTCODEHASH() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = Contract(
        address=Uint160(address),
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    s = State()
    s.universe.add_contract(contract)

    assert (
        concretize(EXTCODEHASH(s, Uint256(address)))
        == 0xD579742AEE22A336CAC42EFE05B2CF1281DB892E213257B929C2338EA0675B00
    )
    assert concretize(EXTCODEHASH(s, Uint256(0x1234))) == 0x0


def test_BLOCKHASH() -> None:
    s = State()
    s.universe.blockhashes = Array.concrete(Uint256, Uint256(0x9999))
    assert concretize(BLOCKHASH(s, s.block.number - Uint256(10))) == 0x9999
    assert concretize(BLOCKHASH(s, s.block.number - Uint256(256))) == 0x9999
    assert concretize(BLOCKHASH(s, s.block.number - Uint256(257))) == 0
    assert concretize(BLOCKHASH(s, s.block.number)) == 0
    assert concretize(BLOCKHASH(s, s.block.number + Uint256(10))) == 0


def test_COINBASE() -> None:
    block = Block(coinbase=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = State(block=block)
    assert concretize(COINBASE(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    block = Block(timestamp=Uint256(1636704767))
    s = State(block=block)
    assert concretize(TIMESTAMP(s)) == 1636704767


def test_NUMBER() -> None:
    block = Block(number=Uint256(1636704767))
    s = State(block=block)
    assert concretize(NUMBER(s)) == 1636704767


def test_PREVRANDAO() -> None:
    block = Block(
        prevrandao=Uint256(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    s = State(block=block)
    assert (
        concretize(PREVRANDAO(s))
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    block = Block(gaslimit=Uint256(0xFFFFFFFFFFFF))
    s = State(block=block)
    assert concretize(GASLIMIT(s)) == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    s = State()
    assert concretize(CHAINID(s)) == 1


def test_BASEFEE() -> None:
    block = Block(basefee=Uint256(10))
    s = State(block=block)
    assert concretize(BASEFEE(s)) == 10


def test_MLOAD() -> None:
    s = State(
        memory=MutableBytes.concrete(
            bytes.fromhex(
                "00000000000000000000000000000000000000000000000000000000000000FF"
            )
        )
    )
    assert concretize(MLOAD(s, Uint256(0))) == 0xFF
    assert concretize(MLOAD(s, Uint256(1))) == 0xFF00


def test_MSTORE() -> None:
    s = State()
    MSTORE(s, Uint256(0), Uint256(0xFF))
    assert (
        s.memory.unwrap().hex()
        == "00000000000000000000000000000000000000000000000000000000000000ff"
    )
    MSTORE(s, Uint256(1), Uint256(0xFF))
    assert (
        s.memory.unwrap().hex()
        == "0000000000000000000000000000000000000000000000000000000000000000ff"
    )


def test_MSTORE8() -> None:
    s = State()
    MSTORE8(s, Uint256(0), Uint256(0xFFFF))

    assert s.memory.unwrap().hex() == "ff"
    MSTORE8(s, Uint256(1), Uint256(0xAABBCCDDEE))
    assert s.memory.unwrap().hex() == "ffee"


def test_SLOAD() -> None:
    s = State()
    s.contract.storage[Uint256(0)] = Uint256(46)
    assert concretize(SLOAD(s, Uint256(0))) == 46
    assert len(s.contract.storage.accessed) == 1
    assert concretize(s.contract.storage.accessed[0]) == 0


def test_SSTORE() -> None:
    s = State()

    SSTORE(s, Uint256(0), Uint256(0xFFFF))
    assert concretize(s.contract.storage[Uint256(0)]) == 0xFFFF

    SSTORE(s, Uint256(8965), Uint256(0xFF))
    assert concretize(s.contract.storage[Uint256(0)]) == 0xFFFF
    assert concretize(s.contract.storage[Uint256(8965)]) == 0xFF


def test_JUMP() -> None:
    contract = Contract(
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    s = State(contract=contract)
    JUMP(s, Uint256(8))
    assert s.pc == 1
    with pytest.raises(KeyError):
        JUMP(s, Uint256(99))


def test_PC() -> None:
    ins = Instruction(0x12, 1, "PC")
    assert concretize(PC(ins)) == 0x12


def test_MSIZE() -> None:
    s = State(memory=MutableBytes.concrete(b"\x00" * 123 + b"\x01"))
    assert concretize(MSIZE(s)) == 124


def test_PUSH() -> None:
    ins = Instruction(0x0, 2, "PUSH", 1, Uint256(0x01))
    assert concretize(PUSH(ins)) == 0x01

    ins = Instruction(0x1, 2, "PUSH", 1)
    with pytest.raises(ValueError):
        PUSH(ins)


def test_DUP() -> None:
    s = State(stack=[Uint256(0x1234)])

    ins = Instruction(0x0, 1, "DUP", 1)
    assert concretize(DUP(ins, s)) == 0x1234

    ins = Instruction(0x0, 1, "DUP")
    with pytest.raises(ValueError):
        DUP(ins, s)


def test_SWAP() -> None:
    s = State(stack=[Uint256(0x1234), Uint256(0x5678)])

    ins = Instruction(0x0, 1, "SWAP", 1)
    SWAP(ins, s)
    stack = [concretize(x) for x in s.stack]
    assert stack == [0x5678, 0x1234]

    ins = Instruction(0x0, 1, "SWAP")
    with pytest.raises(ValueError):
        SWAP(ins, s)


def test_RETURN() -> None:
    s = State(
        latest_return=FrozenBytes.concrete(b"\x12\x34"),
        memory=MutableBytes.concrete(b"\xff\x01"),
    )
    RETURN(s, Uint256(0), Uint256(2))
    assert isinstance(s.pc, Termination)
    assert s.pc.success is True
    assert s.pc.returndata.unwrap() == b"\xff\x01"


def test_REVERT() -> None:
    s = State(
        latest_return=FrozenBytes.concrete(b"\x12\x34"),
        memory=MutableBytes.concrete(b"\xff\x01"),
    )
    REVERT(s, Uint256(0), Uint256(2))
    assert isinstance(s.pc, Termination)
    assert s.pc.success is False
    assert s.pc.returndata.unwrap() == b"\xff\x01"


def test_INVALID() -> None:
    s = State(latest_return=FrozenBytes.concrete(b"\x12\x34"))
    INVALID(s)
    assert isinstance(s.pc, Termination)
    assert s.pc.success is False
    assert s.pc.returndata.unwrap() == b""


def test_SELFDESTRUCT() -> None:
    with pytest.raises(Exception):
        SELFDESTRUCT()
