#!/usr/bin/env pytest

from typing import List

from arrays import FrozenBytes
from disassembler import disassemble
from state import State
from symbolic import BW, unwrap
from testlib import (
    abiencode,
    compile_solidity,
    execute,
    make_contract,
    make_state,
    make_transaction,
)
from vm import printable_execution, step


def concretize_stack(state: State) -> List[int]:
    return [unwrap(x) for x in state.stack]


def test_execute_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 1
    assert state.success is None
    assert concretize_stack(state) == [0xAA]

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 2
    assert state.success is None
    assert concretize_stack(state) == [0xAA, 0x56]

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 3
    assert state.success is None
    assert concretize_stack(state) == [0x100]

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 4
    assert state.success is None
    assert concretize_stack(state) == [0x100, 0x09]

    action = step(state)
    assert action == "JUMPI"
    assert state.pc == 4
    assert state.success is None
    assert concretize_stack(state) == [0x100, 0x09]

    state.pc = program.jumps[0x09]
    assert state.pc == 6
    state.stack = []

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 7
    assert state.success is None
    assert concretize_stack(state) == []

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 8
    assert state.success is None
    assert concretize_stack(state) == [0x00]

    action = step(state)
    assert action == "CONTINUE"
    assert state.pc == 9
    assert state.success is None
    assert concretize_stack(state) == [0x00, 0x00]

    action = step(state)
    assert action == "TERMINATE"
    assert state.success is False
    assert state.returndata.require_concrete() == b""
    assert concretize_stack(state) == []


def test_execute_solidity() -> None:
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
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b"\x00" * 32

    state = make_state(
        contract=state.contract,  # carries forward storage
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("withdraw()")),
        ),
        universe=state.universe,
    )
    execute(state)
    assert state.success is False
    assert state.returndata.require_concrete()[68:91] == b"caller is not the owner"

    state = make_state(
        contract=state.contract,
        transaction=make_transaction(
            callvalue=BW(123456),
            calldata=FrozenBytes.concrete(abiencode("contribute()")),
        ),
        universe=state.universe,
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    state = make_state(
        contract=state.contract,
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
        universe=state.universe,
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete()[-20:] == b"\xca" * 20


def test_output_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
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
