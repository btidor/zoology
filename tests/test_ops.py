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


def test_STOP() -> None:
    s = State(latest_return=FrozenBytes.concrete(b"\x12\x34"))
    STOP(s)
    assert isinstance(s.pc, Termination)
    assert s.pc.success is True
    assert s.pc.returndata.unwrap() == b""


def test_ADD() -> None:
    assert ADD(Uint256(10), Uint256(10)).maybe_unwrap() == 20
    assert (
        ADD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(1),
        ).maybe_unwrap()
        == 0
    )


def test_MUL() -> None:
    assert MUL(Uint256(10), Uint256(10)).maybe_unwrap() == 100
    assert (
        MUL(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(2),
        ).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert SUB(Uint256(10), Uint256(10)).maybe_unwrap() == 0
    assert (
        SUB(Uint256(0), Uint256(1)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert DIV(Uint256(10), Uint256(10)).maybe_unwrap() == 1
    assert DIV(Uint256(1), Uint256(2)).maybe_unwrap() == 0
    assert DIV(Uint256(10), Uint256(0)).maybe_unwrap() == 0


def test_SDIV() -> None:
    assert SDIV(Uint256(10), Uint256(10)).maybe_unwrap() == 1
    assert (
        SDIV(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
        ).maybe_unwrap()
        == 2
    )
    assert SDIV(Uint256(10), Uint256(0)).maybe_unwrap() == 0


def test_MOD() -> None:
    assert MOD(Uint256(10), Uint256(3)).maybe_unwrap() == 1
    assert MOD(Uint256(17), Uint256(5)).maybe_unwrap() == 2
    assert MOD(Uint256(10), Uint256(0)).maybe_unwrap() == 0


def test_SMOD() -> None:
    assert SMOD(Uint256(10), Uint256(3)).maybe_unwrap() == 1
    assert (
        SMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD),
        ).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert SMOD(Uint256(10), Uint256(0)).maybe_unwrap() == 0


def test_ADDMOD() -> None:
    assert ADDMOD(Uint256(10), Uint256(10), Uint256(8)).maybe_unwrap() == 4
    assert (
        ADDMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(2),
            Uint256(2),
        ).maybe_unwrap()
        == 1
    )


def test_MULMOD() -> None:
    assert MULMOD(Uint256(10), Uint256(10), Uint256(8)).maybe_unwrap() == 4
    assert (
        MULMOD(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(12),
        ).maybe_unwrap()
        == 9
    )


def test_EXP() -> None:
    assert EXP(Uint256(10), Uint256(2)).maybe_unwrap() == 100
    assert EXP(Uint256(2), Uint256(2)).maybe_unwrap() == 4


def test_SIGNEXTEND() -> None:
    assert (
        SIGNEXTEND(Uint256(0), Uint256(0xFF)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        SIGNEXTEND(Uint256(0), Uint256(0xAAAA)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert (
        SIGNEXTEND(Uint256(1), Uint256(0xABCD)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFABCD
    )
    assert SIGNEXTEND(Uint256(0), Uint256(0x7F)).maybe_unwrap() == 0x7F
    assert SIGNEXTEND(Uint256(1), Uint256(0x5BCD)).maybe_unwrap() == 0x5BCD
    assert SIGNEXTEND(Uint256(2), Uint256(0xFF)).maybe_unwrap() == 0xFF
    assert SIGNEXTEND(Uint256(2), Uint256(0xABCD)).maybe_unwrap() == 0xABCD
    assert SIGNEXTEND(Uint256(0x7F), Uint256(0x7F)).maybe_unwrap() == 0x7F


def test_LT() -> None:
    assert LT(Uint256(8), Uint256(10)).maybe_unwrap() == 1
    assert LT(Uint256(10), Uint256(10)).maybe_unwrap() == 0


def test_GT() -> None:
    assert GT(Uint256(10), Uint256(8)).maybe_unwrap() == 1
    assert GT(Uint256(10), Uint256(10)).maybe_unwrap() == 0


def test_SLT() -> None:
    assert (
        SLT(
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            Uint256(0),
        ).maybe_unwrap()
        == 1
    )
    assert SLT(Uint256(10), Uint256(10)).maybe_unwrap() == 0


def test_SGT() -> None:
    assert (
        SGT(
            Uint256(0),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
        ).maybe_unwrap()
        == 1
    )
    assert SGT(Uint256(10), Uint256(10)).maybe_unwrap() == 0


def test_EQ() -> None:
    assert EQ(Uint256(10), Uint256(10)).maybe_unwrap() == 1
    assert EQ(Uint256(10), Uint256(8)).maybe_unwrap() == 0


def test_ISZERO() -> None:
    assert ISZERO(Uint256(10)).maybe_unwrap() == 0
    assert ISZERO(Uint256(0)).maybe_unwrap() == 1


def test_AND() -> None:
    assert AND(Uint256(0x0F), Uint256(0x0F)).maybe_unwrap() == 0xF
    assert AND(Uint256(0xFF), Uint256(0)).maybe_unwrap() == 0


def test_OR() -> None:
    assert OR(Uint256(0xF0), Uint256(0x0F)).maybe_unwrap() == 0xFF
    assert OR(Uint256(0xFF), Uint256(0xFF)).maybe_unwrap() == 0xFF


def test_XOR() -> None:
    assert XOR(Uint256(0xF0), Uint256(0x0F)).maybe_unwrap() == 0xFF
    assert XOR(Uint256(0xFF), Uint256(0xFF)).maybe_unwrap() == 0


def test_NOT() -> None:
    assert (
        NOT(Uint256(0)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    assert BYTE(Uint256(31), Uint256(0xFF)).maybe_unwrap() == 0xFF
    assert BYTE(Uint256(30), Uint256(0x8800)).maybe_unwrap() == 0x88
    assert BYTE(Uint256(30), Uint256(0xAABBCC)).maybe_unwrap() == 0xBB
    assert BYTE(Uint256(123456), Uint256(0xAABBCC)).maybe_unwrap() == 0


def test_SHL() -> None:
    assert SHL(Uint256(1), Uint256(1)).maybe_unwrap() == 2
    assert (
        SHL(
            Uint256(4),
            Uint256(0xFF00000000000000000000000000000000000000000000000000000000000000),
        ).maybe_unwrap()
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert SHR(Uint256(1), Uint256(2)).maybe_unwrap() == 1
    assert SHR(Uint256(4), Uint256(0xFF)).maybe_unwrap() == 0xF
    assert SHR(Uint256(123), Uint256(0xAA)).maybe_unwrap() == 0


def test_SAR() -> None:
    assert SAR(Uint256(1), Uint256(2)).maybe_unwrap() == 1
    assert (
        SAR(
            Uint256(4),
            Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0),
        ).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_SHA3() -> None:
    s = State(memory=MutableBytes.concrete(b"\xff\xff\xff\xff"))
    digest = SHA3(s, Uint256(0), Uint256(4))

    solver = Solver()
    s.sha3.constrain(solver)
    assert solver.check()
    assert (
        solver.evaluate(digest)
        == 0x29045A592007D0C246EF02C2223570DA9522D0CF0F73282C79A1BC8F0BB2C238
    )


def test_ADDRESS() -> None:
    contract = Contract(address=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = State(contract=contract)
    assert ADDRESS(s).maybe_unwrap() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    s = State()
    s.universe.balances[Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)] = Uint256(
        125985
    )
    assert (
        BALANCE(s, Uint256(0x9BBFED6889322E016E0A02EE459D306FC19545D8)).maybe_unwrap()
        == 125985
    )


def test_ORIGIN() -> None:
    transaction = Transaction(
        origin=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = State(transaction=transaction)
    assert ORIGIN(s).maybe_unwrap() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    transaction = Transaction(
        caller=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = State(transaction=transaction)
    assert CALLER(s).maybe_unwrap() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    transaction = Transaction(callvalue=Uint256(123456789))
    s = State(transaction=transaction)
    assert CALLVALUE(s).maybe_unwrap() == 123456789


def test_CALLDATALOAD() -> None:
    transaction = Transaction(
        calldata=FrozenBytes.concrete(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    s = State(transaction=transaction)
    assert (
        CALLDATALOAD(s, Uint256(0)).maybe_unwrap()
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        CALLDATALOAD(s, Uint256(31)).maybe_unwrap()
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert CALLDATALOAD(s, Uint256(32)).maybe_unwrap() == 0


def test_CALLDATASIZE() -> None:
    transaction = Transaction(calldata=FrozenBytes.concrete(b"\xff"))
    s = State(transaction=transaction)
    assert CALLDATASIZE(s).maybe_unwrap() == 1


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
    assert CODESIZE(s).maybe_unwrap() == 9


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
    assert GASPRICE(s).maybe_unwrap() == 10


def test_EXTCODESIZE() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = Contract(
        address=Uint160(address),
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    s = State()
    s.universe.add_contract(contract)
    assert EXTCODESIZE(s, Uint256(address)).maybe_unwrap() == 9
    assert EXTCODESIZE(s, Uint256(0x1234)).maybe_unwrap() == 0


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
    assert RETURNDATASIZE(s).maybe_unwrap() == 26


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
        EXTCODEHASH(s, Uint256(address)).maybe_unwrap()
        == 0xD579742AEE22A336CAC42EFE05B2CF1281DB892E213257B929C2338EA0675B00
    )
    assert EXTCODEHASH(s, Uint256(0x1234)).maybe_unwrap() == 0x0


def test_BLOCKHASH() -> None:
    s = State(block=Block(hashes=Array.concrete(Uint8, Uint256(0x9999))))
    assert BLOCKHASH(s, s.block.number - Uint256(10)).maybe_unwrap() == 0x9999
    assert BLOCKHASH(s, s.block.number - Uint256(256)).maybe_unwrap() == 0x9999
    assert BLOCKHASH(s, s.block.number - Uint256(257)).maybe_unwrap() == 0
    assert BLOCKHASH(s, s.block.number).maybe_unwrap() == 0
    assert BLOCKHASH(s, s.block.number + Uint256(10)).maybe_unwrap() == 0


def test_COINBASE() -> None:
    block = Block(coinbase=Uint160(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = State(block=block)
    assert COINBASE(s).maybe_unwrap() == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    block = Block(timestamp=Uint256(1636704767))
    s = State(block=block)
    assert TIMESTAMP(s).maybe_unwrap() == 1636704767


def test_NUMBER() -> None:
    block = Block(number=Uint256(1636704767))
    s = State(block=block)
    assert NUMBER(s).maybe_unwrap() == 1636704767


def test_PREVRANDAO() -> None:
    block = Block(
        prevrandao=Uint256(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    s = State(block=block)
    assert (
        PREVRANDAO(s).maybe_unwrap()
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    block = Block(gaslimit=Uint256(0xFFFFFFFFFFFF))
    s = State(block=block)
    assert GASLIMIT(s).maybe_unwrap() == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    s = State()
    assert CHAINID(s).maybe_unwrap() == 1


def test_BASEFEE() -> None:
    block = Block(basefee=Uint256(10))
    s = State(block=block)
    assert BASEFEE(s).maybe_unwrap() == 10


def test_MLOAD() -> None:
    s = State(
        memory=MutableBytes.concrete(
            bytes.fromhex(
                "00000000000000000000000000000000000000000000000000000000000000FF"
            )
        )
    )
    assert MLOAD(s, Uint256(0)).maybe_unwrap() == 0xFF
    assert MLOAD(s, Uint256(1)).maybe_unwrap() == 0xFF00


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
    assert SLOAD(s, Uint256(0)).maybe_unwrap() == 46
    assert len(s.contract.storage.accessed) == 1
    assert s.contract.storage.accessed[0].maybe_unwrap() == 0


def test_SSTORE() -> None:
    s = State()

    SSTORE(s, Uint256(0), Uint256(0xFFFF))
    assert s.contract.storage[Uint256(0)].maybe_unwrap() == 0xFFFF

    SSTORE(s, Uint256(8965), Uint256(0xFF))
    assert s.contract.storage[Uint256(0)].maybe_unwrap() == 0xFFFF
    assert s.contract.storage[Uint256(8965)].maybe_unwrap() == 0xFF


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
    assert PC(ins).maybe_unwrap() == 0x12


def test_MSIZE() -> None:
    s = State(memory=MutableBytes.concrete(b"\x00" * 123 + b"\x01"))
    assert MSIZE(s).maybe_unwrap() == 124


def test_PUSH() -> None:
    ins = Instruction(0x0, 2, "PUSH", 1, Uint256(0x01))
    assert PUSH(ins).maybe_unwrap() == 0x01

    ins = Instruction(0x1, 2, "PUSH", 1)
    with pytest.raises(ValueError):
        PUSH(ins)


def test_DUP() -> None:
    s = State(stack=[Uint256(0x1234)])

    ins = Instruction(0x0, 1, "DUP", 1)
    assert DUP(ins, s).maybe_unwrap() == 0x1234

    ins = Instruction(0x0, 1, "DUP")
    with pytest.raises(ValueError):
        DUP(ins, s)


def test_SWAP() -> None:
    s = State(stack=[Uint256(0x1234), Uint256(0x5678)])

    ins = Instruction(0x0, 1, "SWAP", 1)
    SWAP(ins, s)
    stack = [x.maybe_unwrap() for x in s.stack]
    assert stack == [0x5678, 0x1234]

    ins = Instruction(0x0, 1, "SWAP")
    with pytest.raises(ValueError):
        SWAP(ins, s)


def test_LOG() -> None:
    s = State(
        stack=[Uint256(0xABCD)],
        memory=MutableBytes.concrete(b"\x12\x34"),
    )
    ins = Instruction(0x0, 1, "LOG", 1)
    LOG(ins, s, Uint256(1), Uint256(1))
    assert len(s.logs) == 1
    assert s.logs[0].data.unwrap() == b"\x34"
    assert len(s.logs[0].topics) == 1
    assert s.logs[0].topics[0].maybe_unwrap() == 0xABCD


def test_CREATE() -> None:
    contract = Contract(
        address=Uint160(0x6AC7EA33F8831EA9DCC53393AAA88B25A785DBF0),
    )
    s = State(
        memory=MutableBytes.concrete(
            b"\xFE\x63\xFF\xFF\xFF\xFF\x60\x00\x52\x60\x04\x60\x1C\xF3"
        ),
        contract=contract,
    )
    flow = CREATE(s, Uint256(999), Uint256(2), Uint256(100))
    assert isinstance(flow, Descend)
    assert (
        flow.state.contract.address.maybe_unwrap()
        == 0x343C43A37D37DFF08AE8C4A11544C718ABB4FCF8
    )
    assert contract.nonce.maybe_unwrap() == 2


def test_RETURN() -> None:
    s = State(
        latest_return=FrozenBytes.concrete(b"\x12\x34"),
        memory=MutableBytes.concrete(b"\xff\x01"),
    )
    RETURN(s, Uint256(0), Uint256(2))
    assert isinstance(s.pc, Termination)
    assert s.pc.success is True
    assert s.pc.returndata.unwrap() == b"\xff\x01"


def test_CREATE2() -> None:
    contract = Contract(address=Uint160(0x0))
    s = State(contract=contract)
    flow = CREATE2(s, Uint256(999), Uint256(0), Uint256(0), Uint256(0x0))
    assert isinstance(flow, Descend)
    assert (
        flow.state.contract.address.maybe_unwrap()
        == 0xE33C0C7F7DF4809055C3EBA6C09CFE4BAF1BD9E0  # from EIP-1014
    )
    assert contract.nonce.maybe_unwrap() == 2


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
