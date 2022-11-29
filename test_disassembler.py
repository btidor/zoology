#!/usr/bin/env pytest

import pytest

from disassembler import disassemble, printable_output


def test_disassemble_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    instructions, jumps = disassemble(code)

    assert len(instructions) == 10

    assert instructions[0].offset == 0
    assert instructions[0].name == "PUSH"
    assert instructions[0].suffix == 1
    assert instructions[0].operand == 0xAA

    assert instructions[4].offset == 7
    assert instructions[4].name == "JUMPI"
    assert instructions[4].suffix is None
    assert instructions[4].operand is None

    assert len(jumps) == 1
    assert jumps[9] == 6


def test_disassemble_suffix() -> None:
    code = bytes.fromhex("63010203048F97")
    instructions, jumps = disassemble(code)

    assert len(instructions) == 3

    assert instructions[0].name == "PUSH"
    assert instructions[0].suffix == 4
    assert instructions[0].operand == 0x01020304

    assert instructions[1].name == "DUP"
    assert instructions[1].suffix == 16
    assert instructions[1].operand is None

    assert instructions[2].name == "SWAP"
    assert instructions[2].suffix == 8
    assert instructions[2].operand is None

    assert len(jumps) == 0


def test_disassemble_trailer() -> None:
    code = bytes.fromhex("60FEFE97FE0F")
    instructions, jumps = disassemble(code)

    assert len(instructions) == 2

    assert instructions[0].name == "PUSH"
    assert instructions[0].operand == 0xFE

    assert instructions[1].name == "INVALID"

    assert len(jumps) == 0


def test_disassemble_invalid() -> None:
    with pytest.raises(ValueError):
        disassemble(b"\x0F")


def test_output_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    instructions, _ = disassemble(code)
    output = printable_output(instructions)

    fixture = """
        0000  PUSH1\t0xaa
        0002  PUSH1\t0x56
        0004  ADD
        0005  PUSH1\t0x09
        0007  JUMPI
        0008  STOP
        0009  JUMPDEST
        000a  PUSH1\t0x00
        000c  PUSH1\t0x00
        000e  REVERT\n"""
    fixture = fixture.replace("\n        ", "\n")[1:]

    print(fixture)
    print(output)
    assert output == fixture
