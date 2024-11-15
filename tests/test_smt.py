#!/usr/bin/env pytest

from zbitvector import Solver

from bytes import Bytes
from smt import (
    Array,
    Uint8,
    Uint64,
    Uint256,
    bvadd_harder,
    bvlshr_harder,
    concat_bytes,
    explode_bytes,
)


def test_bvlshr_harder():
    assert bvlshr_harder(Uint256(0x1234), Uint256(1)).reveal() == 0x91A
    assert bvlshr_harder(Uint256(0x1234), Uint256(4)).reveal() == 0x123
    assert bvlshr_harder(Uint256(0x1234), Uint256(0)).reveal() == 0x1234
    assert bvlshr_harder(Uint256(0x1234), Uint256(257)).reveal() == 0

    a = Array[Uint256, Uint256]("BVLSHR0")
    b = Bytes(explode_bytes(a[Uint256(0)]))
    q = concat_bytes(
        Uint8(0x12),
        Uint8(0x34),
        Uint8(0x56),
        Uint8(0x78),
        *(b[Uint256(i)] for i in range(28)),
    )
    assert (
        bvlshr_harder(
            q,
            Uint256(0xE0),
        ).reveal()
        == 0x12345678
    )
    assert (
        bvlshr_harder(
            q,
            Uint256(0xE4),
        ).reveal()
        == 0x1234567
    )
    assert (
        bvlshr_harder(
            q,
            Uint256(0x123),
        ).reveal()
        == 0
    )


def test_bvadd_harder():
    assert bvadd_harder(Uint256(0x1234), Uint256(0x5678)).reveal() == 0x68AC

    solver = Solver()
    a = Uint64("BVADD0").into(Uint256)
    for i in range(256):
        z = Uint256(1 << i)
        assert not solver.check(bvadd_harder(a, z) != (a + z))
        assert not solver.check(bvadd_harder(z, a) != (a + z))

    b: Uint64 = concat_bytes(
        Uint8("BVADD1"),
        Uint8("BVADD2"),
        *(Uint8(i * 0x11) for i in range(6)),
    )
    assert not solver.check(bvadd_harder(b, Uint64(1)) != (b + Uint64(1)))
    assert not solver.check(bvadd_harder(Uint64(1), b) != (b + Uint64(1)))

    c: Uint64 = concat_bytes(
        *(Uint8(0xFF) for _ in range(7)),
        Uint8("BVADD3"),
    )
    assert not solver.check(bvadd_harder(c, Uint64(1)) != (c + Uint64(1)))
    assert not solver.check(bvadd_harder(Uint64(1), c) != (c + Uint64(1)))

    assert not solver.check(
        bvadd_harder(a, Uint256(0xFFFFFFFFFFFF)) != (a + Uint256(0xFFFFFFFFFFFF))
    )
    assert not solver.check(
        bvadd_harder(Uint256(0xFFFFFFFFFFFF), a) != (a + Uint256(0xFFFFFFFFFFFF))
    )

    assert str(bvadd_harder(a, Uint256(1))).startswith("Uint256(`(concat #b0000")
