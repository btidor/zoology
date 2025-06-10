#!/usr/bin/env pytest

from typing import Any, Callable

import pytest

from bytes import Bytes
from smt import Array, Uint8, Uint256
from smt2.analyze_composite import COMPOSITE_PY, Compositor
from smt2.analyze_minmax import MinMaxCase, MinMaxCaseParser
from smt2.analyze_rewrite import CaseParser, RewriteCase
from smt2.minmax import constraint_minmax, propagate_minmax
from smt2.rewrite import (
    bitvector_folding,
    bitvector_logic,
    bitvector_reduction,
    constraint_folding,
    constraint_logic,
    constraint_reduction,
)
from smt2.theory_core import CSymbol, Distinct, Not, check


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
    term1 = Not(Not(CSymbol(b"X")))
    term2 = CSymbol(b"X")
    assert not check(Distinct(term1, term2))


# SMT Test for Rewrite Rules


def parameterize_rewrite(rw: Callable[..., Any]) -> Any:
    return pytest.mark.parametrize(
        "case", map(lambda c: pytest.param(c, id=c.id), RewriteCase.from_function(rw))
    )


@parameterize_rewrite(constraint_reduction)
def test_constraint_reduction(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@parameterize_rewrite(constraint_folding)
def test_constraint_folding(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@parameterize_rewrite(constraint_logic)
def test_constraint_logic(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@parameterize_rewrite(bitvector_reduction)
def test_bitvector_reduction(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@parameterize_rewrite(bitvector_folding)
def test_bitvector_folding(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@parameterize_rewrite(bitvector_logic)
def test_bitvector_logic(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


@pytest.mark.parametrize(
    "case",
    map(lambda c: pytest.param(c, id=c.id), MinMaxCase.from_function(propagate_minmax)),
)
def test_propagate_minmax(case: MinMaxCase):
    assert MinMaxCaseParser.is_sound(case)


@parameterize_rewrite(constraint_minmax)
def test_constraint_minmax(case: RewriteCase):
    assert CaseParser.is_equivalent(case)


def test_codegen():
    with open(COMPOSITE_PY) as f:
        actual = f.read()
    expected = Compositor.dump()
    assert actual == expected, "please run `python3 -m smt2.analyze_composite`"
