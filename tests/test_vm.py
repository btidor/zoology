#!/usr/bin/env pytest

from bytes import Bytes
from compiler import compile
from disassembler import abiencode, disassemble
from smt import Array, Uint160, Uint256
from state import Block, Contract, Terminus
from vm import execute, translate

from .solidity import load_binary, load_solidity, loads_solidity

DEFAULT_ADDRESS = 0xADADADADADADADADADADADADADADADADADADADAD


def test_basic() -> None:
    code = Bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    states = list(compile(program))
    assert len(states) == 1

    state = translate(
        states[0],
        Block.sample(0),
        Bytes(),
        Uint256(0),
        Array[Uint256, Uint256](Uint256(0)),
    )
    assert isinstance(state.pc, Terminus)
    assert not state.pc.success
    assert state.pc.returndata.reveal() == b""


def test_fallback() -> None:
    contracts = {
        DEFAULT_ADDRESS: Contract(
            address=Uint160(DEFAULT_ADDRESS),
            program=load_solidity("fixtures/01_Fallback.sol"),
        )
    }
    calldata = abiencode("owner()")
    state, _ = execute(contracts, DEFAULT_ADDRESS, calldata, 0, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (0).to_bytes(32)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    calldata = abiencode("Fal1out()")
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal() == 0xCACACACACACACACACACACACACACACACACACACACA
    )


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    calldata = abiencode("flip(bool)") + (0).to_bytes(32)
    storage = {
        2: 0x8000000000000000000000000000000000000000000000000000000000000000,
    }
    state = _execute(program, calldata, storage)

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal()
        == 0x8B1A944CF13A9A1C08FACB2C9E98623EF3254D2DDB48113885C3E8E97FEC8DB9
    )


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    calldata = abiencode("changeOwner(address)") + (
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    ).to_bytes(32)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    calldata = (
        abiencode("transfer(address,uint256)")
        + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
        + (0xEEEE).to_bytes(32)
    )
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_delegation() -> None:
    program = loads_solidity("fixtures/06_Delegation.sol")["Delegation"]
    calldata = abiencode("pwn()")
    # storage.poke(Uint256(1), addresses["Delegate"].into(Uint256))
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    # callvalue = Uint256(0x1234)
    state = _execute(program, b"", {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is False
    assert state.pc.returndata.reveal() == b""


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    calldata = abiencode("unlock(bytes32)") + (0).to_bytes(32)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    # callvalue = Uint256(0x1234)
    state = _execute(program, b"", {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    calldata = abiencode("donate(address)") + (1).to_bytes(32)
    # callvalue = Uint256(0x1234)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


# def test_elevator() -> None:
#     contracts, addresses = contracts_multiple("fixtures/11_Elevator.sol")
#     state = State(
#         transaction=Transaction(
#             caller=addresses["TestBuilding"],
#             calldata=Bytes(abiencode("goTo(uint256)") + (1).to_bytes(32)),
#             address=addresses["Elevator"],
#         ),
#         contracts=contracts,
#     )
#     state = _execute(program, calldata, {})

#     assert isinstance(state.pc, Termination)
#     assert state.pc.success is True
#     assert state.pc.returndata.reveal() == b""


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    calldata = abiencode("unlock(bytes16)") + (0x4321 << 128).to_bytes(32)
    storage = {5: 0x4321 << 128}
    state = _execute(program, calldata, storage)

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


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
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Terminus)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


# def test_preservation() -> None:
#     contracts, addresses = contracts_multiple("fixtures/15_Preservation.sol")
#     state = State(
#         transaction=Transaction(
#             calldata=Bytes(abiencode("setFirstTime(uint256)") + (0x5050).to_bytes(32)),
#             address=addresses["Preservation"],
#         ),
#         contracts=contracts,
#     )
#     state.storage.poke(Uint256(0), addresses["LibraryContract"].into(Uint256))
#     state.storage.poke(Uint256(1), addresses["LibraryContract"].into(Uint256))

#     state = _execute(program, calldata, {})

#     assert isinstance(state.pc, Termination)
#     assert state.pc.success is True
#     assert state.pc.returndata.reveal() == b""
