#!/usr/bin/env pytest

from bytes import Bytes
from compiler import compile
from disassembler import Program, abiencode, disassemble
from smt import Array, Solver, Uint256
from state import Block, State, Termination
from vm import execute

from .solidity import load_binary, load_solidity, loads_solidity


def test_basic() -> None:
    code = Bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    states = list(compile(program))
    assert len(states) == 1

    state = execute(
        states[0], Block.sample(0), Bytes(), Array[Uint256, Uint256](Uint256(0))
    )
    assert isinstance(state.pc, Termination)
    assert not state.pc.success
    assert state.pc.returndata.reveal() == b""


def _execute(program: Program, calldata: bytes, storage: dict[int, int]) -> State:
    block, input = Block.sample(0), Bytes(calldata)
    store = Array[Uint256, Uint256](Uint256(0))
    for key, value in storage.items():
        store[Uint256(key)] = Uint256(value)

    found = None
    for state in compile(program):
        state = execute(state, block, input, store)

        solver = Solver()
        solver.add(state.constraint)
        if not solver.check():
            pass
        elif found is None:
            found = state
        else:
            raise RuntimeError("found multiple states")
    if found is None:
        raise RuntimeError("no states found")
    return found


def test_fallback() -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    calldata = abiencode("owner()")
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (0).to_bytes(32)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    calldata = abiencode("Fal1out()")
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal() == 0xCACACACACACACACACACACACACACACACACACACACA
    )


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    calldata = abiencode("flip(bool)") + (0).to_bytes(32)
    storage = {
        1: 0xFEDC,
        2: 57896044618658097711785492504343953926634992332820282019728792003956564819968,
    }
    state = _execute(program, calldata, storage)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal()
        == 0x1F6D785BDB6AE9ECE46F3323FB3289240BD2D1C4C683CF558EE200C89933DF4F
    )


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    calldata = abiencode("changeOwner(address)") + (
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    ).to_bytes(32)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
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

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_delegation() -> None:
    program = loads_solidity("fixtures/06_Delegation.sol")["Delegation"]
    calldata = abiencode("pwn()")
    # storage.poke(Uint256(1), addresses["Delegate"].into(Uint256))
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    # callvalue = Uint256(0x1234)
    state = _execute(program, b"", {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.reveal() == b""


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    calldata = abiencode("unlock(bytes32)") + (0).to_bytes(32)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    # callvalue = Uint256(0x1234)
    state = _execute(program, b"", {})

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    calldata = abiencode("donate(address)") + (1).to_bytes(32)
    # callvalue = Uint256(0x1234)
    state = _execute(program, calldata, {})

    assert isinstance(state.pc, Termination)
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

    assert isinstance(state.pc, Termination)
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

    assert isinstance(state.pc, Termination)
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
