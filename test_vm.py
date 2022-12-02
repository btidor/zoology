#!/usr/bin/env pytest

from typing import List, assert_never

from _state import State
from _symbolic import BW, ByteArray, require_concrete
from disassembler import disassemble
from testlib import abiencode, compile_solidity, make_contract, make_state
from vm import _concrete_JUMPI, printable_execution, step


def concretize_stack(state: State) -> List[int]:
    return [require_concrete(x) for x in state.stack]


def concretize_returndata(state: State) -> bytes:
    return bytes(require_concrete(x) for x in state.returndata)


def execute(state: State) -> None:
    while True:
        action = step(state)
        if action == "CONTINUE":
            continue
        elif action == "JUMPI":
            _concrete_JUMPI(state)
        elif action == "TERMINATE":
            return
        else:
            assert_never(action)


def test_execute_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = make_state(
        contract=make_contract(program=program),
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", b""),
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
    assert state.returndata == []
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
    code = compile_solidity(source, "0.8.17")
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", abiencode("owner()")),
    )
    execute(state)
    assert state.success is True
    assert concretize_returndata(state) == b"\x00" * 32

    state = make_state(
        contract=state.contract,  # carries forward storage
        universe=state.universe,
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", abiencode("withdraw()")),
    )
    execute(state)
    assert state.success is False
    assert concretize_returndata(state)[68:91] == b"caller is not the owner"

    state = make_state(
        contract=state.contract,
        universe=state.universe,
        callvalue=BW(123456),
        calldata=ByteArray("CALLDATA", abiencode("contribute()")),
    )
    execute(state)
    assert state.success is True
    assert concretize_returndata(state) == b""

    state = make_state(
        contract=state.contract,
        universe=state.universe,
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", abiencode("owner()")),
    )
    execute(state)
    assert state.success is True
    assert concretize_returndata(state)[-20:] == b"\xcc" * 20


def test_output_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    state = make_state(
        contract=make_contract(program=program),
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", b""),
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
