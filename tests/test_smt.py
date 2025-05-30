#!/usr/bin/env pytest

from typing import Any, Callable

import pytest

from bytes import Bytes
from smt import Array, Uint8, Uint256
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
    b = Bytes(Uint8.explode(a[Uint256(0)]))
    q = Uint256.concat(
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


# SMT Test for Rewrite Rules

MAX_WIDTH = 65


def check_case(ctx: CaseParser) -> None:
    for ctx in ctx.parse_pattern():
        ctx.parse_guard()
        ctx.parse_body()
        assert ctx.equivalent()


def parameterize(rw: Callable[..., Any]) -> Any:
    return pytest.mark.parametrize(
        "case", map(lambda c: pytest.param(c, id=c.id), Casette.from_function(rw))
    )


@parameterize(rewrite_constraint)
def test_rewrite_constraint(case: Casette):
    check_case(CaseParser(case, None))


@parameterize(rewrite_bitvector)
def test_rewrite_bitvector(case: Casette):
    for width in range(1, MAX_WIDTH):
        check_case(CaseParser(case, width))


@parameterize(rewrite_mixed)
def test_rewrite_mixed(case: Casette):
    for width in range(1, MAX_WIDTH):
        check_case(CaseParser(case, width))
