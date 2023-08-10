#!/usr/bin/env pytest

from bytes import FrozenBytes
from disassembler import abiencode, disassemble
from environment import Contract, Transaction
from smt.smt import Uint160, Uint256
from state import State, Termination
from vm import printable_execution, step

from .solidity import compile_solidity, load_binary, load_solidity, loads_solidity


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
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(),
    )

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
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b"\x00" * 32

    state = State(
        contract=state.contract,  # carries forward storage
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("withdraw()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert (data := state.pc.returndata.reveal()) is not None
    assert data[68:91] == b"caller is not the owner"

    state = State(
        contract=state.contract,
        transaction=Transaction(
            callvalue=Uint256(123456),
            calldata=FrozenBytes.concrete(abiencode("contribute()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""

    state = State(
        contract=state.contract,
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (data := state.pc.returndata.reveal()) is not None
    assert data[-20:] == b"\xca" * 20


def test_basic_printable() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(),
    )

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
    program = load_solidity("fixtures/01_Fallback.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (0).to_bytes(32)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("Fal1out()")),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.contract.storage[Uint256(1)].reveal()
        == 0xCACACACACACACACACACACACACACACACACACACACA
    )


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("flip(bool)") + (0).to_bytes(32)),
        ),
    )
    state.contract.storage[Uint256(1)] = Uint256(0xFEDC)
    state.contract.storage[Uint256(2)] = Uint256(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert (
        state.contract.storage[Uint256(1)].reveal()
        == 0x1F6D785BDB6AE9ECE46F3323FB3289240BD2D1C4C683CF558EE200C89933DF4F
    )


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            caller=Uint160(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            calldata=FrozenBytes.concrete(
                abiencode("changeOwner(address)")
                + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(
                abiencode("transfer(address,uint256)")
                + (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).to_bytes(32)
                + ((0xEEEE).to_bytes(32))
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")

    other = Contract(address=Uint160(0xABCDEF), program=programs["Delegate"])
    state = State(
        contract=Contract(program=programs["Delegation"]),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(abiencode("pwn()")),
        ),
    )
    state.universe.add_contract(other)
    state.contract.storage.poke(Uint256(1), other.address.into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(callvalue=Uint256(0x1234)),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.reveal() == b""


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes32)") + (0).to_bytes(32)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(callvalue=Uint256(0x1234)),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(
                abiencode("donate(address)") + (1).to_bytes(32)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")

    state = State(
        contract=Contract(program=programs["Elevator"]),
        transaction=Transaction(
            caller=Uint160(0x76543210),
            calldata=FrozenBytes.concrete(
                abiencode("goTo(uint256)") + (1).to_bytes(32)
            ),
        ),
    )
    state.universe.add_contract(
        Contract(address=Uint160(0x76543210), program=programs["TestBuilding"])
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes16)") + (0x4321 << 128).to_bytes(32)
            ),
        ),
    )
    state.contract.storage.poke(Uint256(5), Uint256(0x4321 << 128))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""


def test_gatekeeper_one() -> None:
    # We can't execute GatekeeperOne because concrete gas isn't implemented.
    # Instead, just check that it compiles.
    _ = load_solidity("fixtures/13_GatekeeperOne.sol")


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    state = State(
        contract=Contract(program=program),
        transaction=Transaction(
            calldata=FrozenBytes.concrete(
                abiencode("enter(bytes8)")
                + bytes.fromhex(
                    "65d5bd2c953ab27b000000000000000000000000000000000000000000000000"
                )
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == (1).to_bytes(32)


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    preservation = Contract(program=programs["Preservation"])
    library = Contract(
        address=Uint160(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    state = State(
        contract=preservation,
        transaction=Transaction(
            calldata=FrozenBytes.concrete(
                abiencode("setFirstTime(uint256)") + (0x5050).to_bytes(32)
            ),
        ),
    )
    state.universe.add_contract(library)
    state.contract.storage.poke(Uint256(0), library.address.into(Uint256))
    state.contract.storage.poke(Uint256(1), library.address.into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.reveal() == b""
