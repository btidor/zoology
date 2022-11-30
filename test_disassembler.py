#!/usr/bin/env pytest

import pytest

from disassembler import disassemble, printable_output


def test_disassemble_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    p = disassemble(code)

    assert len(p.instructions) == 10

    assert p.instructions[0].offset == 0
    assert p.instructions[0].name == "PUSH"
    assert p.instructions[0].suffix == 1
    assert p.instructions[0].operand == 0xAA

    assert p.instructions[4].offset == 7
    assert p.instructions[4].name == "JUMPI"
    assert p.instructions[4].suffix is None
    assert p.instructions[4].operand is None

    assert len(p.jumps) == 1
    assert p.jumps[9] == 6


def test_disassemble_suffix() -> None:
    code = bytes.fromhex("63010203048F97")
    p = disassemble(code)

    assert len(p.instructions) == 3

    assert p.instructions[0].name == "PUSH"
    assert p.instructions[0].suffix == 4
    assert p.instructions[0].operand == 0x01020304

    assert p.instructions[1].name == "DUP"
    assert p.instructions[1].suffix == 16
    assert p.instructions[1].operand is None

    assert p.instructions[2].name == "SWAP"
    assert p.instructions[2].suffix == 8
    assert p.instructions[2].operand is None

    assert len(p.jumps) == 0


def test_disassemble_trailer() -> None:
    code = bytes.fromhex("60FEFE97FE0F")
    p = disassemble(code)

    assert len(p.instructions) == 2

    assert p.instructions[0].name == "PUSH"
    assert p.instructions[0].operand == 0xFE

    assert p.instructions[1].name == "INVALID"

    assert len(p.jumps) == 0


def test_disassemble_invalid() -> None:
    with pytest.raises(ValueError):
        disassemble(b"\x0F")


def test_output_basic() -> None:
    code = bytes.fromhex("60AA605601600957005B60006000FD")
    raw = """
        0000  PUSH1\t0xaa
        0002  PUSH1\t0x56
        0004  ADD
        0005  PUSH1\t0x09
        0007  JUMPI
        0008  STOP
        0009  JUMPDEST
        000a  PUSH1\t0x00
        000c  PUSH1\t0x00
        000e  REVERT""".splitlines()
    fixture = map(lambda x: x.strip(), raw[1:])

    for actual, expected in zip(printable_output(code), fixture):
        print(actual, expected)
        assert actual == expected
