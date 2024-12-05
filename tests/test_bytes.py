#!/usr/bin/env pytest

from bytes import Bytes, Memory
from smt import Uint8, Uint64, Uint256


def test_memory_simplify():
    memory = Memory()
    memory[Uint256(0x20)] = Uint8(0x11)
    memory[Uint256(0x40)] = Uint8(0x22)
    assert memory[Uint256(0x20)].reveal() == 0x11

    ptr = Uint256(0x40) + Uint64("BYTES0").into(Uint256)
    memory[ptr] = Uint8(0x33)
    assert memory[ptr].reveal() == 0x33
    assert memory[Uint256(0x20)].reveal() == 0x11
    assert (
        str(memory[Uint256(0x40)])
        == "Uint8(`(let (($e1 (concat #x000000000000000000000000000000000000000000000000 BYTES0))) (ite (and (bvult #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd #x0000000000000000000000000000000000000000000000000000000000000041 $e1)) (not (bvult #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd #x0000000000000000000000000000000000000000000000000000000000000040 $e1)))) #x33 #x22))`)"
    )


def test_memory_slice():
    memory = Memory()
    memory[Uint256(0x20)] = Uint8(0x11)
    memory[Uint256(0x40)] = Uint8(0x22)
    assert memory[Uint256(0x00)].reveal() == 0x00
    assert memory[Uint256(0x20)].reveal() == 0x11
    assert memory[Uint256(0x40)].reveal() == 0x22
    assert memory[Uint256(0x60)].reveal() == 0x00

    slice = Bytes.symbolic("BYTES1")
    slice = slice.slice(Uint256(0), slice.length)
    memory.graft(slice, Uint256(0x60))
    assert memory[Uint256(0x00)].reveal() == 0x00
    assert memory[Uint256(0x20)].reveal() == 0x11
    assert memory[Uint256(0x40)].reveal() == 0x22
    assert (
        str(memory[Uint256(0x60)])
        == "Uint8(`(let (($e1 (concat #x000000000000000000000000000000000000000000000000 BYTES1.length))) (ite (and (not (= #x0000000000000000000000000000000000000000000000000000000000000000 $e1)) (bvult #x0000000000000000000000000000000000000000000000000000000000000060 (bvadd #x0000000000000000000000000000000000000000000000000000000000000060 $e1))) (select BYTES1 #x0000000000000000000000000000000000000000000000000000000000000000) #x00))`)"
    )

    free = Uint256(0x60) + slice.length
    memory[free] = Uint8(0x33)
    assert memory[Uint256(0x00)].reveal() == 0x00
    assert memory[Uint256(0x20)].reveal() == 0x11
    assert memory[Uint256(0x40)].reveal() == 0x22
    # raise NotImplementedError(memory[Uint256(0x60)])
    # # TODO:
    # assert (
    #     str(memory[Uint256(0x60)])
    #     == "Uint8(`(let (($e1 (concat #x000000000000000000000000000000000000000000000000 BYTES1.length))) (ite (and (not (= #x0000000000000000000000000000000000000000000000000000000000000000 $e1)) (bvult #x0000000000000000000000000000000000000000000000000000000000000060 (bvadd #x0000000000000000000000000000000000000000000000000000000000000060 $e1))) (select BYTES1 #x0000000000000000000000000000000000000000000000000000000000000000) #x00))`)"
    # )
    assert memory[free].reveal() == 0x33
