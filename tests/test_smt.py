#!/usr/bin/env pytest

import z3  # pyright: ignore[reportMissingTypeStubs]

from bytes import Bytes
from smt import (
    Array,
    Uint8,
    Uint256,
    concat_bytes,
    explode_bytes,
)
from smt2._base import DumpContext
from smt2._constraint import Constraint, Not, Symbol, Xor


def test_bvlshr_harder():
    assert (Uint256(0x1234) >> Uint256(1)).reveal() == 0x91A
    assert (Uint256(0x1234) >> Uint256(4)).reveal() == 0x123
    assert (Uint256(0x1234) >> Uint256(0)).reveal() == 0x1234
    assert (Uint256(0x1234) >> Uint256(257)).reveal() == 0

    a = Array[Uint256, Uint256]("BVLSHR0")
    b = Bytes(explode_bytes(a[Uint256(0)]))
    q = concat_bytes(
        Uint8(0x12),
        Uint8(0x34),
        Uint8(0x56),
        Uint8(0x78),
        *(b[Uint256(i)] for i in range(28)),
    )
    assert (q >> Uint256(0xE0)).reveal() == 0x12345678
    assert (q >> Uint256(0xE4)).reveal() == 0x1234567
    assert (q >> Uint256(0x123)).reveal() == 0


def _assert_equiv(term1: Constraint, term2: Constraint):
    cmp = Xor(term1, term2)

    ctx = DumpContext()
    ctx.write(b"(assert ")
    cmp._dump(ctx)  # pyright: ignore[reportPrivateUsage]
    ctx.write(b")")
    smt = b"\n".join((*ctx.defs.values(), bytes(ctx.out))).decode()
    # print(smt)

    s = z3.Solver()
    s.add(z3.parse_smt2_string(smt))  # pyright: ignore[reportUnknownMemberType]
    assert s.check() == z3.unsat  # pyright: ignore[reportUnknownMemberType]


def test_rewrite_constraint():
    term1 = Not(Not(Symbol("X")))
    term2 = Symbol("X")
    _assert_equiv(term1, term2)
