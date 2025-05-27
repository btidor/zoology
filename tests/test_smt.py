#!/usr/bin/env pytest

import pytest

from bytes import Bytes
from smt import (
    Array,
    Uint8,
    Uint256,
    concat_bytes,
    explode_bytes,
)
from smt2._analysis import ParsedCase, PreCase
from smt2._core import Distinct, Not, Symbol, check
from smt2._core import rewrite as rewrite_constraint


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


def test_simple_rewrite():
    term1 = Not(Not(Symbol(b"X")))
    term2 = Symbol(b"X")
    assert not check(Distinct(term1, term2))


@pytest.mark.parametrize("case", PreCase.from_function(rewrite_constraint))
def test_rewrite_constraint(case: PreCase):
    ctx = ParsedCase(case)
    for term1, subctx in ctx.parse_pattern():
        term2 = subctx.parse_body()
        assert not check(Distinct(term1, term2), *subctx.constraints)
