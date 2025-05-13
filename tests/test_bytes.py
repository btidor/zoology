#!/usr/bin/env pytest

from bytes import Bytes, Memory
from smt import Int256, Uint8, Uint64, Uint256


def test_memory_simplify():
    memory = Memory()
    memory[Uint256(0x20)] = Uint8(0x11)
    memory[Uint256(0x40)] = Uint8(0x22)
    assert memory[Uint256(0x20)].reveal() == 0x11

    ptr = Uint256(0x60) + Uint64("BYTES0").into(Uint256)
    memory[ptr] = Uint8(0x33)
    assert memory[ptr].reveal() == 0x33
    assert memory[Uint256(0x20)].reveal() == 0x11


def test_memory_slice():
    memory = Memory()
    memory[Uint256(0x20)] = Uint8(0x11)
    memory[Uint256(0x40)] = Uint8(0x22)
    assert memory[Uint256(0x20)].reveal() == 0x11

    bytes = Bytes.symbolic("BYTES1")
    slice = bytes.slice(Uint256(0), bytes.length)
    memory.graft(slice, Uint256(0x60))
    assert memory[Uint256(0x20)].reveal() == 0x11

    free = Uint256(0x60) + bytes.length
    memory[free] = Uint8(0x33)
    assert memory[free].reveal() == 0x33
    assert memory[Uint256(0x20)].reveal() == 0x11


def test_memory_arith():
    base = Uint256(0x60) + Uint64("BYTES0").into(Uint256)
    offset = base + Uint256(0x20)

    delta = offset - base
    assert delta.reveal() == 0x20

    delta = Uint256(0x20) - base
    assert (delta.into(Int256) < Int256(0)).reveal() is True
