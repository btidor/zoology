#!/usr/bin/env pytest

from bytes import Bytes
from disassembler import abiencode, disassemble
from environment import Transaction
from smt import Uint160, Uint256
from state import State, Termination
from vm import printable_execution, step

from .solidity import (
    compile_solidity,
    universe_binary,
    universe_multiple,
    universe_single,
)


def concretize_stack(state: State) -> list[int]:
    return [v for v in (x.reveal() for x in state.stack) if v is not None]


def execute(state: State) -> State:
    generator = printable_execution(state)
    try:
        while True:
            next(generator)
    except StopIteration as e:
        assert isinstance(e.value, State)
        return e.value


def test_basic() -> None:
    code = Bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = State().with_contract(program)

    action = step(state)
    assert action is None
    assert state.pc == 1
    assert concretize_stack(state) == [0xAA]

    action = step(state)
    assert action is None
    assert state.pc == 2
    assert concretize_stack(state) == [0xAA, 0x56]

    action = step(state)
    assert action is None
    assert state.pc == 3
    assert concretize_stack(state) == [0x100]

    action = step(state)
    assert action is None
    assert state.pc == 4
    assert concretize_stack(state) == [0x100, 0x09]

    action = step(state)
    assert action is None  # internally-handled JUMPI
    assert state.pc == 6
    assert concretize_stack(state) == []

    action = step(state)
    assert action is None
    assert state.pc == 7
    assert concretize_stack(state) == []

    action = step(state)
    assert action is None
    assert state.pc == 8
    assert concretize_stack(state) == [0x00]

    action = step(state)
    assert action is None
    assert state.pc == 9
    assert concretize_stack(state) == [0x00, 0x00]

    action = step(state)
    assert action is None
    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.reveal() == b""
    assert concretize_stack(state) == []


def test_basic_solidity() -> None:
    # https://ethernaut.openzeppelin.com/level/0x80934BE6B8B872B364b470Ca30EaAd8AEAC4f63F
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Fallback {
            mapping(address => uint) public contributions;
            address public owner;

            constructor() {
                owner = msg.sender;
                contributions[msg.sender] = 1000 * (1 ether);
            }

            modifier onlyOwner {
                        require(
                                msg.sender == owner,
                                "caller is not the owner"
                        );
                        _;
                }

            function contribute() public payable {
                require(msg.value < 0.001 ether);
                contributions[msg.sender] += msg.value;
                if(contributions[msg.sender] > contributions[owner]) {
                    owner = msg.sender;
                }
            }

            function getContribution() public view returns (uint) {
                return contributions[msg.sender];
            }

            function withdraw() public onlyOwner {
                payable(owner).transfer(address(this).balance);
            }

            receive() external payable {
                require(msg.value > 0 && contributions[msg.sender] > 0);
                owner = msg.sender;
            }
        }
    """
    code = compile_solidity(source)
    program = disassemble(code["Fallback"])

    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("owner()")),
        ),
    ).with_contract(program)

    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b"\x00" * 32

    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("withdraw()")),
        ),
        universe=state.universe,  # carries forward storage
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert (data := state.pc.returndata.reveal()) is not None
    assert data[68:91] == b"caller is not the owner"

    state = State(
        transaction=Transaction(
            callvalue=Uint256(123456),
            calldata=Bytes(abiencode("contribute()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""

    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("owner()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (data := state.pc.returndata.reveal()) is not None
    assert data[-20:] == b"\xca" * 20


def test_basic_printable() -> None:
    code = Bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = State().with_contract(program)

    raw = """
        0000  PUSH1\t0xaa
          00000000000000000000000000000000000000000000000000000000000000aa

        0002  PUSH1\t0x56
          00000000000000000000000000000000000000000000000000000000000000aa
          0000000000000000000000000000000000000000000000000000000000000056

        0004  ADD
          0000000000000000000000000000000000000000000000000000000000000100

        0005  PUSH1\t0x09
          0000000000000000000000000000000000000000000000000000000000000100
          0000000000000000000000000000000000000000000000000000000000000009

        0007  JUMPI

        0009  JUMPDEST

        000a  PUSH1\t0x00
          0000000000000000000000000000000000000000000000000000000000000000

        000c  PUSH1\t0x00
          0000000000000000000000000000000000000000000000000000000000000000
          0000000000000000000000000000000000000000000000000000000000000000

        000e  REVERT

        REVERT b''""".splitlines()
    fixture = map(lambda x: x[8:], raw[1:])

    for actual, expected in zip(printable_execution(state), fixture, strict=True):
        assert actual == expected


def test_fallback() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("owner()")),
        ),
        universe=universe_single("fixtures/01_Fallback.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (0).to_bytes(32)


def test_fallout() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("Fal1out()")),
        ),
        universe=universe_single("fixtures/02_Fallout.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal() == 0xCACACACACACACACACACACACACACACACACACACACA
    )


def test_coinflip() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("flip(bool)") + (0).to_bytes(32)),
        ),
        universe=universe_single("fixtures/03_CoinFlip.sol"),
    )
    state.storage[Uint256(1)] = Uint256(0xFEDC)
    state.storage[Uint256(2)] = Uint256(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.storage[Uint256(1)].reveal()
        == 0x1F6D785BDB6AE9ECE46F3323FB3289240BD2D1C4C683CF558EE200C89933DF4F
    )


def test_telephone() -> None:
    state = State(
        transaction=Transaction(
            caller=Uint160(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            calldata=Bytes(
                abiencode("changeOwner(address)")
                + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
            ),
        ),
        universe=universe_single("fixtures/04_Telephone.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_token() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(
                abiencode("transfer(address,uint256)")
                + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
                + (0xEEEE).to_bytes(32)
            ),
        ),
        universe=universe_single("fixtures/05_Token.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_delegation() -> None:
    universe, addresses = universe_multiple("fixtures/06_Delegation.sol")
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("pwn()")),
            address=addresses["Delegation"],
        ),
        universe=universe,
    )
    state.storage.poke(Uint256(1), addresses["Delegate"].into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_force() -> None:
    state = State(
        transaction=Transaction(callvalue=Uint256(0x1234)),
        universe=universe_binary("fixtures/07_Force.bin"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.reveal() == b""


def test_vault() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("unlock(bytes32)") + (0).to_bytes(32)),
        ),
        universe=universe_single("fixtures/08_Vault.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_king() -> None:
    state = State(
        transaction=Transaction(callvalue=Uint256(0x1234)),
        universe=universe_single("fixtures/09_King.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_reentrancy() -> None:
    state = State(
        transaction=Transaction(
            callvalue=Uint256(0x1234),
            calldata=Bytes(abiencode("donate(address)") + (1).to_bytes(32)),
        ),
        universe=universe_single("fixtures/10_Reentrancy.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_elevator() -> None:
    universe, addresses = universe_multiple("fixtures/11_Elevator.sol")
    state = State(
        transaction=Transaction(
            caller=addresses["TestBuilding"],
            calldata=Bytes(abiencode("goTo(uint256)") + (1).to_bytes(32)),
            address=addresses["Elevator"],
        ),
        universe=universe,
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_privacy() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("unlock(bytes16)") + (0x4321 << 128).to_bytes(32)),
        ),
        universe=universe_binary("fixtures/12_Privacy.bin"),
    )
    state.storage.poke(Uint256(5), Uint256(0x4321 << 128))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_gatekeeper_one() -> None:
    # We can't execute GatekeeperOne because concrete gas isn't implemented.
    # Instead, just check that it compiles.
    _ = universe_single("fixtures/13_GatekeeperOne.sol")


def test_gatekeeper_two() -> None:
    state = State(
        transaction=Transaction(
            calldata=Bytes(
                abiencode("enter(bytes8)")
                + bytes.fromhex(
                    "65d5bd2c953ab27b000000000000000000000000000000000000000000000000"
                )
            ),
        ),
        universe=universe_single("fixtures/14_GatekeeperTwo.sol"),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_preservation() -> None:
    universe, addresses = universe_multiple("fixtures/15_Preservation.sol")
    state = State(
        transaction=Transaction(
            calldata=Bytes(abiencode("setFirstTime(uint256)") + (0x5050).to_bytes(32)),
            address=addresses["Preservation"],
        ),
        universe=universe,
    )
    state.storage.poke(Uint256(0), addresses["LibraryContract"].into(Uint256))
    state.storage.poke(Uint256(1), addresses["LibraryContract"].into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""
