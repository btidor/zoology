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
from smt2.analysis import CaseParser, Casette
from smt2.core import Distinct, Not, Symbol, check
from smt2.rwbv import rewrite_bitvector, rewrite_mixed
from smt2.rwcore import rewrite_constraint


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


@pytest.mark.parametrize("case", Casette.from_function(rewrite_constraint))
def test_rewrite_constraint(case: Casette):
    _check_case(CaseParser(case, None))


@pytest.mark.parametrize("case", Casette.from_function(rewrite_bitvector))
def test_rewrite_bitvector(case: Casette):
    for width in range(1, 65):
        _check_case(CaseParser(case, width))


@pytest.mark.parametrize("case", Casette.from_function(rewrite_mixed))
def test_rewrite_mixed(case: Casette):
    for width in range(1, 65):
        _check_case(CaseParser(case, width))


def _check_case(ctx: CaseParser) -> None:
    for ctx in ctx.parse_pattern():
        ctx.parse_guard()
        ctx.parse_body()
        assert ctx.equivalent()
