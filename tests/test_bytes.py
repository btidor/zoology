#!/usr/bin/env pytest

from bytes import Memory
from smt import Uint8, Uint64, Uint256


def test_memory_simplify():
    memory = Memory()
    memory[Uint256(0x20)] = Uint8(0x11)
    memory[Uint256(0x40)] = Uint8(0x22)
    assert memory[Uint256(0x20)].reveal() == 0x11

    ptr = Uint256(0x60) + Uint64("BYTES0").into(Uint256)
    memory[ptr] = Uint8(0x33)
    assert memory[ptr].reveal() == 0x33
    # assert memory[Uint256(0x20)].reveal() == 0x11  # :(
