#!/usr/bin/env pytest

import pytest

from bytes import Bytes
from compiler import Terminus, compile, symbolic_block, symbolic_transaction
from disassembler import Program, abiencode, disassemble
from environ import Address, Block, Blockchain, Contract, Transaction
from smt import Array, Uint160, Uint256
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from vm import execute, handle_hypercalls, substitutions

from .solidity import load_binary, load_solidity, loads_solidity

ADDRESS = Address(0xADADADADADADADADADADADADADADADADADADADAD)


def test_basic() -> None:
    code = Bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)

    k = Blockchain()
    k.contracts[ADDRESS] = Contract(program)

    terms = list(compile(program))
    assert len(terms) == 1

    subs = substitutions(symbolic_block(), Block()) + substitutions(
        symbolic_transaction(), Transaction()
    )
    term = terms[0].substitute(subs)
    assert not term.success
    assert term.returndata.reveal() == b""


@pytest.mark.parametrize("i,factory", list(enumerate(LEVEL_FACTORIES)))
def test_snapshot(i: int, factory: Address) -> None:
    k = snapshot_contracts(factory)
    tx = Transaction(
        address=Uint160(factory),
        calldata=Bytes(abiencode("createInstance(address)") + (0xB).to_bytes(32)),
        callvalue=Uint256(10**15),
    )
    k.balances[tx.address] = Uint256(10**15)
    k, term = execute(k, tx)
    assert term.success, f"Level {i}: {term.returndata.reveal()}"


def _execute_compiled(
    program: Program, calldata: bytes = b"", callvalue: int = 0
) -> Terminus:
    k = Blockchain()
    k.contracts = {ADDRESS: Contract(program)}
    k.balances[Uint160(ADDRESS)] = Uint256(10**15)
    block = Block()
    tx = Transaction(
        address=Uint160(ADDRESS),
        callvalue=Uint256(callvalue),
        calldata=Bytes(calldata),
    )

    address = Address.unwrap(tx.address, "execute")
    program = k.contracts[address].program
    subs = [
        *substitutions(symbolic_block(), block),
        *substitutions(symbolic_transaction(), tx),
        (Array[Uint256, Uint256]("STORAGE"), k.contracts[address].storage),
    ]

    for term in compile(program):
        term = term.substitute(subs)
        k, term = handle_hypercalls(k, tx, block, term)

        assert (ok := term.path.constraint.reveal()) is not None
        if ok:
            if term.storage:
                k.contracts[address].storage = term.storage
            return term
    raise RuntimeError("no termination matched")


def test_fallback() -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    calldata = abiencode("owner()")
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.returndata.reveal() == (0).to_bytes(32)
    assert term.storage is None


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    calldata = abiencode("Fal1out()")
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.storage is not None
    assert (
        term.storage[Uint256(1)].reveal() == 0xCACACACACACACACACACACACACACACACACACACACA
    )


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    k = Blockchain(contracts={ADDRESS: Contract(program)})
    k.contracts[ADDRESS].storage[Uint256(2)] = Uint256(
        0x8000000000000000000000000000000000000000000000000000000000000000
    )

    tx = Transaction(
        address=Uint160(ADDRESS),
        calldata=Bytes(abiencode("flip(bool)") + (0).to_bytes(32)),
    )
    _, term = execute(k, tx)

    assert term.success is True
    assert term.storage is not None
    assert (
        term.storage[Uint256(1)].reveal()
        == 0x8B1A944CF13A9A1C08FACB2C9E98623EF3254D2DDB48113885C3E8E97FEC8DB9
    )


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    calldata = abiencode("changeOwner(address)") + (
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    ).to_bytes(32)
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.returndata.reveal() == b""
    assert term.storage is not None


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    calldata = (
        abiencode("transfer(address,uint256)")
        + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
        + (0xEEEE).to_bytes(32)
    )
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.returndata.reveal() == (1).to_bytes(32)
    assert term.storage is not None


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")
    k = Blockchain(
        contracts={
            ADDRESS: Contract(programs["Delegation"]),
            Address(0x8001): Contract(programs["Delegate"]),
        }
    )
    k.contracts[ADDRESS].storage[Uint256(1)] = Uint256(0x8001)
    k.balances[Uint160(ADDRESS)] = Uint256(10**15)

    tx = Transaction(
        address=Uint160(ADDRESS),
        calldata=Bytes(abiencode("pwn()")),
    )
    _, term = execute(k, tx)

    assert term.success is True
    assert term.returndata.reveal() == b""
    assert term.storage is not None


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    term = _execute_compiled(program, callvalue=0x1234)

    assert term.success is False
    assert term.returndata.reveal() == b""
    assert term.storage is None


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    calldata = abiencode("unlock(bytes32)") + (0).to_bytes(32)
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.returndata.reveal() == b""
    assert term.storage is not None


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    term = _execute_compiled(program, callvalue=0x1234)

    assert term.success is True
    assert term.returndata.reveal() == b""
    assert term.storage is not None


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    calldata = abiencode("donate(address)") + (1).to_bytes(32)
    term = _execute_compiled(program, calldata, callvalue=0x1234)

    assert term.success is True
    assert term.returndata.reveal() == b""


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")
    caller = Address(0xCACACACACACACACACACACACACACACACACACACACA)
    k = Blockchain(
        contracts={
            caller: Contract(programs["TestBuilding"]),
            ADDRESS: Contract(programs["Elevator"]),
        }
    )
    k.balances[Uint160(ADDRESS)] = Uint256(10**15)

    tx = Transaction(
        address=Uint160(ADDRESS),
        calldata=Bytes(abiencode("goTo(uint256)") + (1).to_bytes(32)),
    )
    _, term = execute(k, tx)

    assert term.success is True
    assert term.returndata.reveal() == b""


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    k = Blockchain(contracts={ADDRESS: Contract(program)})
    k.contracts[ADDRESS].storage[Uint256(5)] = Uint256(0x4321 << 128)

    tx = Transaction(
        address=Uint160(ADDRESS),
        calldata=Bytes(abiencode("unlock(bytes16)") + (0x4321 << 128).to_bytes(32)),
    )
    _, term = execute(k, tx)

    assert term.success is True
    assert term.returndata.reveal() == b""
    term = _execute_compiled(program, callvalue=0x1234)


def test_gatekeeper_one() -> None:
    # We can't execute GatekeeperOne because concrete gas isn't implemented.
    # Instead, just check that it compiles.
    program = load_solidity("fixtures/13_GatekeeperOne.sol")
    for _ in compile(program):
        pass


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    calldata = abiencode("enter(bytes8)") + bytes.fromhex(
        "65d5bd2c953ab27b000000000000000000000000000000000000000000000000"
    )
    term = _execute_compiled(program, calldata)

    assert term.success is True
    assert term.returndata.reveal() == (1).to_bytes(32)
    term = _execute_compiled(program, callvalue=0x1234)


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    library = Address(0x12345678)
    k = Blockchain(
        contracts={
            ADDRESS: Contract(programs["Preservation"]),
            library: Contract(programs["LibraryContract"]),
        }
    )
    k.contracts[ADDRESS].storage[Uint256(0)] = Uint256(library)
    k.contracts[ADDRESS].storage[Uint256(1)] = Uint256(library)
    k.balances[Uint160(ADDRESS)] = Uint256(10**15)

    tx = Transaction(
        address=Uint160(ADDRESS),
        calldata=Bytes(abiencode("setFirstTime(uint256)") + (0x5050).to_bytes(32)),
    )
    _, term = execute(k, tx)

    assert term.success is True
    assert term.returndata.reveal() == b""
