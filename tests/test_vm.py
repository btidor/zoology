#!/usr/bin/env pytest

from arrays import FrozenBytes
from disassembler import disassemble
from smt import Uint160, Uint256
from solidity import (
    abiencode,
    compile_solidity,
    load_binary,
    load_solidity,
    loads_solidity,
)
from state import Jump, State, Termination
from testlib import make_contract, make_state, make_transaction
from vm import printable_execution, step


def concretize_stack(state: State) -> list[int]:
    return [x.unwrap() for x in state.stack]


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
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(b""),
        ),
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
    assert isinstance(action, Jump)
    assert len(action.targets) == 2
    constraint, state = action.targets[0]
    assert constraint.unwrap() is False
    assert state.pc == 5
    constraint, state = action.targets[1]
    assert constraint.unwrap() is True
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
    assert state.pc.returndata.unwrap() == b""
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

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b"\x00" * 32

    state = make_state(
        contract=state.contract,  # carries forward storage
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("withdraw()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.unwrap()[68:91] == b"caller is not the owner"

    state = make_state(
        contract=state.contract,
        transaction=make_transaction(
            callvalue=Uint256(123456),
            calldata=FrozenBytes.concrete(abiencode("contribute()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""

    state = make_state(
        contract=state.contract,
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
        universe=state.universe,
    )
    state = execute(state)
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap()[-20:] == b"\xca" * 20


def test_basic_printable() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(b""),
        ),
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
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == Uint256(0).unwrap(bytes)


def test_fallout() -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("Fal1out()")),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.contract.storage[Uint256(1)].unwrap(bytes) == Uint256(
        0xCACACACACACACACACACACACACACACACACACACACA
    ).unwrap(bytes)


def test_coinflip() -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("flip(bool)") + Uint256(0).unwrap(bytes)
            ),
        ),
    )
    state.contract.storage[Uint256(1)] = Uint256(0xFEDC)
    state.contract.storage[Uint256(2)] = Uint256(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.contract.storage[Uint256(1)].unwrap(bytes) == Uint256(0).unwrap(bytes)


def test_telephone() -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            caller=Uint160(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("changeOwner(address)")
                + Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).unwrap(bytes)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_token() -> None:
    program = load_solidity("fixtures/05_Token.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("transfer(address,uint256)")
                + Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).unwrap(bytes)
                + Uint256(0xEEEE).unwrap(bytes)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == Uint256(1).unwrap(bytes)


def test_delegation() -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")

    other = make_contract(address=Uint160(0xABCDEF), program=programs["Delegate"])
    state = make_state(
        contract=make_contract(program=programs["Delegation"]),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("pwn()")),
        ),
    )
    state.universe.add_contract(other)
    state.contract.storage.poke(Uint256(1), other.address.into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_force() -> None:
    program = load_binary("fixtures/07_Force.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is False
    assert state.pc.returndata.unwrap() == b""


def test_vault() -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes32)") + Uint256(0).unwrap(bytes)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_king() -> None:
    program = load_solidity("fixtures/09_King.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_reentrancy() -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(
                abiencode("donate(address)") + Uint256(1).unwrap(bytes)
            ),
        ),
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_elevator() -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")

    state = make_state(
        contract=make_contract(program=programs["Elevator"]),
        transaction=make_transaction(
            caller=Uint160(0x76543210),
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("goTo(uint256)") + Uint256(1).unwrap(bytes)
            ),
        ),
    )
    state.universe.add_contract(
        make_contract(address=Uint160(0x76543210), program=programs["TestBuilding"])
    )

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_privacy() -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes16)") + Uint256(0x4321 << 128).unwrap(bytes)
            ),
        ),
    )
    state.contract.storage.poke(Uint256(5), Uint256(0x4321 << 128))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""


def test_gatekeeper_one() -> None:
    # We can't execute GatekeeperOne because concrete gas isn't implemented.
    # Instead, just check that it compiles.
    _ = load_solidity("fixtures/13_GatekeeperOne.sol")


def test_gatekeeper_two() -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
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
    assert state.pc.returndata.unwrap() == Uint256(1).unwrap(bytes)


def test_preservation() -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    preservation = make_contract(program=programs["Preservation"])
    library = make_contract(
        address=Uint160(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    state = make_state(
        contract=preservation,
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("setFirstTime(uint256)") + Uint256(0x5050).unwrap(bytes)
            ),
        ),
    )
    state.universe.add_contract(library)
    state.contract.storage.poke(Uint256(0), library.address.into(Uint256))
    state.contract.storage.poke(Uint256(1), library.address.into(Uint256))

    state = execute(state)

    assert isinstance(state.pc, Termination)
    assert state.pc.success is True
    assert state.pc.returndata.unwrap() == b""
