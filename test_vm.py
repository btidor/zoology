#!/usr/bin/env pytest

from typing import List

from common import BW, Block, ByteArray, State, require_concrete
from disassembler import disassemble
from vm import printable_execution, step


def concretize_stack(state: State) -> List[int]:
    return [require_concrete(x) for x in state.stack]


def test_execute_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    block = Block()
    state = State(
        callvalue=BW(0),
        calldata=ByteArray("CALLDATA", b""),
    )

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 1
    assert state.success is None
    assert concretize_stack(state) == [0xAA]

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 2
    assert state.success is None
    assert concretize_stack(state) == [0xAA, 0x56]

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 3
    assert state.success is None
    assert concretize_stack(state) == [0x100]

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 4
    assert state.success is None
    assert concretize_stack(state) == [0x100, 0x09]

    action = step(program, block, state)
    assert action == "JUMPI"
    assert state.pc == 4
    assert state.success is None
    assert concretize_stack(state) == [0x100, 0x09]

    state.pc = program.jumps[0x09]
    assert state.pc == 6
    state.stack = []

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 7
    assert state.success is None
    assert concretize_stack(state) == []

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 8
    assert state.success is None
    assert concretize_stack(state) == [0x00]

    action = step(program, block, state)
    assert action == "CONTINUE"
    assert state.pc == 9
    assert state.success is None
    assert concretize_stack(state) == [0x00, 0x00]

    action = step(program, block, state)
    assert action == "TERMINATE"
    assert state.success == False
    assert concretize_stack(state) == []


def test_output_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    program = disassemble(code)
    block = Block()
    state = State(
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

    for actual, expected in zip(
        printable_execution(program, block, state), fixture, strict=True
    ):
        assert actual == expected
