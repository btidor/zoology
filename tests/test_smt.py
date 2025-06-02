#!/usr/bin/env pytest

from typing import Any, Callable

import pytest

from bytes import Bytes
from smt import Array, Uint8, Uint256
from smt2.analysis import CaseParser, Casette
from smt2.rewrite_bitvec import rewrite_bitvector, rewrite_mixed
from smt2.rewrite_core import rewrite_constraint
from smt2.theory_core import Distinct, Not, Symbol, check


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

MAX_WIDTH = 8


def parameterize(rw: Callable[..., Any]) -> Any:
    return pytest.mark.parametrize(
        "case", map(lambda c: pytest.param(c, id=c.id), Casette.from_function(rw))
    )


@parameterize(rewrite_constraint)
def test_rewrite_constraint(case: Casette):
    assert CaseParser(case, None).is_equivalent()


@parameterize(rewrite_bitvector)
def test_rewrite_bitvector(case: Casette):
    for width in range(1, MAX_WIDTH + 1):
        assert CaseParser(case, width).is_equivalent()


@parameterize(rewrite_mixed)
def test_rewrite_mixed(case: Casette):
    for width in range(1, MAX_WIDTH + 1):
        assert CaseParser(case, width).is_equivalent()
