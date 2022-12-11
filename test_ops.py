#!/usr/bin/env pytest

import pytest
import z3

from disassembler import Instruction, disassemble
from ops import *
from state import State
from symbolic import BA, BW, BY, Bytes, check, simplify, unwrap_bytes
from testlib import (
    make_block,
    make_contract,
    make_state,
    make_transaction,
    make_universe,
)


def _dump_memory(s: State) -> str:
    v = ""
    lim = max(s.memory.keys())
    for i in range(lim + 1):
        v += unwrap_bytes(s.memory.get(i, BY(0))).hex()
    return "0x" + v.upper()


def test_STOP() -> None:
    s = make_state(returndata=Bytes.concrete(b"\x12\x34"))
    STOP(s)
    assert s.success is True
    assert s.returndata.require_concrete() == b""


def test_ADD() -> None:
    assert simplify(ADD(BW(10), BW(10))) == 20
    assert (
        simplify(
            ADD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(1),
            )
        )
        == 0
    )


def test_MUL() -> None:
    assert simplify(MUL(BW(10), BW(10))) == 100
    assert (
        simplify(
            MUL(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(2),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )


def test_SUB() -> None:
    assert simplify(SUB(BW(10), BW(10))) == 0
    assert (
        simplify(SUB(BW(0), BW(1)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_DIV() -> None:
    assert simplify(DIV(BW(10), BW(10))) == 1
    assert simplify(DIV(BW(1), BW(2))) == 0
    assert simplify(DIV(BW(10), BW(0))) == 0


def test_SDIV() -> None:
    assert simplify(SDIV(BW(10), BW(10))) == 1
    assert (
        simplify(
            SDIV(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            )
        )
        == 2
    )
    assert simplify(SDIV(BW(10), BW(0))) == 0


def test_MOD() -> None:
    assert simplify(MOD(BW(10), BW(3))) == 1
    assert simplify(MOD(BW(17), BW(5))) == 2
    assert simplify(MOD(BW(10), BW(0))) == 0


def test_SMOD() -> None:
    assert simplify(SMOD(BW(10), BW(3))) == 1
    assert (
        simplify(
            SMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF8),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD),
            )
        )
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    )
    assert simplify(SMOD(BW(10), BW(0))) == 0


def test_ADDMOD() -> None:
    assert simplify(ADDMOD(BW(10), BW(10), BW(8))) == 4
    assert (
        simplify(
            ADDMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(2),
                BW(2),
            )
        )
        == 1
    )


def test_MULMOD() -> None:
    assert simplify(MULMOD(BW(10), BW(10), BW(8))) == 4
    assert (
        simplify(
            MULMOD(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(12),
            )
        )
        == 9
    )


def test_EXP() -> None:
    assert simplify(EXP(BW(10), BW(2))) == 100
    assert simplify(EXP(BW(2), BW(2))) == 4


def test_SIGNEXTEND() -> None:
    assert (
        simplify(SIGNEXTEND(BW(0), BW(0xFF)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        simplify(SIGNEXTEND(BW(0), BW(0xAA)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAA
    )
    assert simplify(SIGNEXTEND(BW(0), BW(0x7F))) == 0x7F
    assert simplify(SIGNEXTEND(BW(2), BW(0xFF))) == 0xFF
    assert simplify(SIGNEXTEND(BW(0x7F), BW(0x7F))) == 0x7F


def test_LT() -> None:
    assert simplify(LT(BW(8), BW(10))) == 1
    assert simplify(LT(BW(10), BW(10))) == 0


def test_GT() -> None:
    assert simplify(GT(BW(10), BW(8))) == 1
    assert simplify(GT(BW(10), BW(10))) == 0


def test_SLT() -> None:
    assert (
        simplify(
            SLT(
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
                BW(0),
            )
        )
        == 1
    )
    assert simplify(SLT(BW(10), BW(10))) == 0


def test_SGT() -> None:
    assert (
        simplify(
            SGT(
                BW(0),
                BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF),
            )
        )
        == 1
    )
    assert simplify(SGT(BW(10), BW(10))) == 0


def test_EQ() -> None:
    assert simplify(EQ(BW(10), BW(10))) == 1
    assert simplify(EQ(BW(10), BW(8))) == 0


def test_ISZERO() -> None:
    assert simplify(ISZERO(BW(10))) == 0
    assert simplify(ISZERO(BW(0))) == 1


def test_AND() -> None:
    assert simplify(AND(BW(0x0F), BW(0x0F))) == 0xF
    assert simplify(AND(BW(0xFF), BW(0))) == 0


def test_OR() -> None:
    assert simplify(OR(BW(0xF0), BW(0x0F))) == 0xFF
    assert simplify(OR(BW(0xFF), BW(0xFF))) == 0xFF


def test_XOR() -> None:
    assert simplify(XOR(BW(0xF0), BW(0x0F))) == 0xFF
    assert simplify(XOR(BW(0xFF), BW(0xFF))) == 0


def test_NOT() -> None:
    assert (
        simplify(NOT(BW(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )


def test_BYTE() -> None:
    assert simplify(BYTE(BW(31), BW(0xFF))) == 0xFF
    assert simplify(BYTE(BW(30), BW(0x8800))) == 0x88
    assert simplify(BYTE(BW(30), BW(0xAABBCC))) == 0xBB
    assert simplify(BYTE(BW(123456), BW(0xAABBCC))) == 0


def test_SHL() -> None:
    assert simplify(SHL(BW(1), BW(1))) == 2
    assert (
        simplify(
            SHL(
                BW(4),
                BW(0xFF00000000000000000000000000000000000000000000000000000000000000),
            )
        )
        == 0xF000000000000000000000000000000000000000000000000000000000000000
    )


def test_SHR() -> None:
    assert simplify(SHR(BW(1), BW(2))) == 1
    assert simplify(SHR(BW(4), BW(0xFF))) == 0xF
    assert simplify(SHR(BW(123), BW(0xAA))) == 0


def test_SAR() -> None:
    assert simplify(SAR(BW(1), BW(2))) == 1
    assert (
        simplify(
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
    contract = make_contract(address=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = make_state(contract=contract)
    assert simplify(ADDRESS(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_BALANCE() -> None:
    s = make_state()
    s.universe.balances[BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8)] = BW(125985)
    assert (
        simplify(BALANCE(s, BW(0x9BBFED6889322E016E0A02EE459D306FC19545D8))) == 125985
    )


def test_ORIGIN() -> None:
    transaction = make_transaction(
        origin=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = make_state(transaction=transaction)
    assert simplify(ORIGIN(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLER() -> None:
    transaction = make_transaction(
        caller=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8)
    )
    s = make_state(transaction=transaction)
    assert simplify(CALLER(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_CALLVALUE() -> None:
    transaction = make_transaction(callvalue=BW(123456789))
    s = make_state(transaction=transaction)
    assert simplify(CALLVALUE(s)) == 123456789


def test_CALLDATALOAD() -> None:
    transaction = make_transaction(
        calldata=Bytes.concrete(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    s = make_state(transaction=transaction)
    assert (
        simplify(CALLDATALOAD(s, BW(0)))
        == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    )
    assert (
        simplify(CALLDATALOAD(s, BW(31)))
        == 0xFF00000000000000000000000000000000000000000000000000000000000000
    )
    assert simplify(CALLDATALOAD(s, BW(32))) == 0


def test_CALLDATASIZE() -> None:
    transaction = make_transaction(calldata=Bytes.concrete(b"\xff"))
    s = make_state(transaction=transaction)
    assert CALLDATASIZE(s) == 1


def test_CALLDATACOPY() -> None:
    transaction = make_transaction(
        calldata=Bytes.concrete(
            b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"
        )
    )
    s = make_state(transaction=transaction)

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
    s = make_state(
        contract=make_contract(
            program=disassemble(bytes.fromhex("66000000000000005B")),
        )
    )
    assert CODESIZE(s) == 9


def test_CODECOPY() -> None:
    s = make_state(
        contract=make_contract(
            program=disassemble(bytes.fromhex("66000000000000005B")),
        )
    )

    CODECOPY(s, BW(0), BW(0), BW(0x09))
    assert _dump_memory(s) == "0x66000000000000005B"

    CODECOPY(s, BW(1), BW(8), BW(0x20))
    assert (
        _dump_memory(s)
        == "0x665B00000000000000000000000000000000000000000000000000000000000000"
    )


def test_GASPRICE() -> None:
    transaction = make_transaction(gasprice=BW(10))
    s = make_state(transaction=transaction)
    assert simplify(GASPRICE(s)) == 10


def test_EXTCODESIZE() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = make_contract(
        address=BA(address), program=disassemble(bytes.fromhex("66000000000000005B"))
    )
    s = make_state(universe=make_universe(contracts={address: contract}))
    assert EXTCODESIZE(s, BA(address)) == 9
    assert EXTCODESIZE(s, BA(0x1234)) == 0


def test_EXTCODECOPY() -> None:
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = make_contract(
        address=BA(address), program=disassemble(bytes.fromhex("66000000000000005B"))
    )
    s = make_state(universe=make_universe(contracts={address: contract}))

    EXTCODECOPY(s, BA(address), BW(3), BW(5), BW(7))
    assert _dump_memory(s) == "0x0000000000005B000000"

    EXTCODECOPY(s, BA(0x1234), BW(0), BW(0), BW(10))
    assert _dump_memory(s) == "0x00000000000000000000"


def test_RETURNDATASIZE() -> None:
    s = make_state(returndata=Bytes.concrete(b"abcdefghijklmnopqrstuvwxyz"))
    assert simplify(RETURNDATASIZE(s)) == 26


def test_RETURNDATACOPY() -> None:
    s = make_state(
        returndata=Bytes.concrete(
            b"\x7d\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x7f"
        )
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


def test_EXTCODEHASH() -> None:  # TODO
    address = 0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD
    contract = make_contract(
        address=BA(address), program=disassemble(bytes.fromhex("66000000000000005B"))
    )
    s = make_state(universe=make_universe(contracts={address: contract}))

    assert (
        EXTCODEHASH(s, BA(address))
        == 0xD579742AEE22A336CAC42EFE05B2CF1281DB892E213257B929C2338EA0675B00
    )
    assert EXTCODEHASH(s, BA(0x1234)) == 0x0


def test_BLOCKHASH() -> None:
    s = make_state()
    s.universe.blockhashes.array = z3.K(z3.BitVecSort(256), BW(0x9999))
    assert simplify(BLOCKHASH(s, s.block.number - 10)) == 0x9999
    assert simplify(BLOCKHASH(s, s.block.number - 256)) == 0x9999
    assert simplify(BLOCKHASH(s, s.block.number - 257)) == 0
    assert simplify(BLOCKHASH(s, s.block.number)) == 0
    assert simplify(BLOCKHASH(s, s.block.number + 10)) == 0


def test_COINBASE() -> None:
    block = make_block(coinbase=BA(0x9BBFED6889322E016E0A02EE459D306FC19545D8))
    s = make_state(block=block)
    assert simplify(COINBASE(s)) == 0x9BBFED6889322E016E0A02EE459D306FC19545D8


def test_TIMESTAMP() -> None:
    block = make_block(timestamp=BW(1636704767))
    s = make_state(block=block)
    assert simplify(TIMESTAMP(s)) == 1636704767


def test_NUMBER() -> None:
    block = make_block(number=BW(1636704767))
    s = make_state(block=block)
    assert simplify(NUMBER(s)) == 1636704767


def test_PREVRANDAO() -> None:
    block = make_block(
        prevrandao=BW(
            0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
        )
    )
    s = make_state(block=block)
    assert (
        simplify(PREVRANDAO(s))
        == 0xCE124DEE50136F3F93F19667FB4198C6B94EECBACFA300469E5280012757BE94
    )


def test_GASLIMIT() -> None:
    block = make_block(gaslimit=BW(0xFFFFFFFFFFFF))
    s = make_state(block=block)
    assert simplify(GASLIMIT(s)) == 0xFFFFFFFFFFFF


def test_CHAINID() -> None:
    s = make_state()
    assert CHAINID(s) == 1


def test_BASEFEE() -> None:
    block = make_block(basefee=BW(10))
    s = make_state(block=block)
    assert simplify(BASEFEE(s)) == 10


def test_MLOAD() -> None:
    s = make_state(memory={31: BY(0xFF)})
    assert simplify(MLOAD(s, BW(0))) == 0xFF
    assert simplify(MLOAD(s, BW(1))) == 0xFF00


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
    s = make_state()
    s.contract.storage[BW(0)] = BW(46)
    assert simplify(SLOAD(s, BW(0))) == 46
    assert len(s.contract.storage.accessed) == 1
    assert simplify(s.contract.storage.accessed[0]) == 0


def test_SSTORE() -> None:
    s = make_state()

    SSTORE(s, BW(0), BW(0xFFFF))
    assert simplify(s.contract.storage[BW(0)]) == 0xFFFF

    SSTORE(s, BW(8965), BW(0xFF))
    assert simplify(s.contract.storage[BW(0)]) == 0xFFFF
    assert simplify(s.contract.storage[BW(8965)]) == 0xFF


def test_JUMP() -> None:
    contract = make_contract(
        program=disassemble(bytes.fromhex("66000000000000005B")),
    )
    print(contract.program)
    s = make_state(contract=contract)
    JUMP(s, BW(8))
    assert s.pc == 1
    with pytest.raises(KeyError):
        JUMP(s, BW(99))


def test_PC() -> None:
    ins = Instruction(0x12, 1, "PC")
    assert simplify(PC(ins)) == 0x12


def test_MSIZE() -> None:
    s = make_state(memory={123: BY(0x01)})
    assert simplify(MSIZE(s)) == 124


def test_PUSH() -> None:
    ins = Instruction(0x0, 2, "PUSH", 1, BW(0x01))
    assert simplify(PUSH(ins)) == 0x01

    ins = Instruction(0x1, 2, "PUSH", 1)
    with pytest.raises(ValueError):
        PUSH(ins)


def test_DUP() -> None:
    s = make_state(stack=[BW(0x1234)])

    ins = Instruction(0x0, 1, "DUP", 1)
    assert simplify(DUP(ins, s)) == 0x1234

    ins = Instruction(0x0, 1, "DUP")
    with pytest.raises(ValueError):
        DUP(ins, s)


def test_SWAP() -> None:
    s = make_state(stack=[BW(0x1234), BW(0x5678)])

    ins = Instruction(0x0, 1, "SWAP", 1)
    SWAP(ins, s)
    stack = [simplify(x) for x in s.stack]
    assert stack == [0x5678, 0x1234]

    ins = Instruction(0x0, 1, "SWAP")
    with pytest.raises(ValueError):
        SWAP(ins, s)


def test_CALL() -> None:
    s = make_state(returndata=Bytes.concrete(b"\x01"))
    s.universe.balances[s.contract.address] = BW(125)
    res = CALL(s, BW(0), BW(0x1234), BW(123), BW(0), BW(0), BW(0), BW(0))
    assert simplify(res) == 1
    assert s.returndata.require_concrete() == b""
    assert simplify(s.universe.balances[BA(0x1234)]) == 123
    assert simplify(s.universe.balances[s.contract.address]) == 2


def test_RETURN() -> None:
    s = make_state(
        returndata=Bytes.concrete(b"\x12\x34"),
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    RETURN(s, BW(0), BW(2))
    assert s.success is True
    assert s.returndata.require_concrete() == b"\xff\x01"


def test_REVERT() -> None:
    s = make_state(
        returndata=Bytes.concrete(b"\x12\x34"),
        memory={0: BY(0xFF), 1: BY(0x01)},
    )
    REVERT(s, BW(0), BW(2))
    assert s.success is False
    assert s.returndata.require_concrete() == b"\xff\x01"


def test_INVALID() -> None:
    s = make_state(returndata=Bytes.concrete(b"\x12\x34"))
    INVALID(s)
    assert s.success is False
    assert s.returndata.require_concrete() == b""


def test_SELFDESTRUCT() -> None:
    with pytest.raises(Exception):
        SELFDESTRUCT()
