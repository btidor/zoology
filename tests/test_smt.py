#!/usr/bin/env pytest

from bytes import Bytes
from smt import (
    Array,
    Uint8,
    Uint256,
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
