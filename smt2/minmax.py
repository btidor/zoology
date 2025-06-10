"""
Library for min-max tracking of bitvector terms.

For each term, interpreted as an unsigned integer, `minmax()` propagates the
minimum and maximum value of the term across operations.
"""
# ruff: noqa: F403, F405

from __future__ import annotations

from .theory_bitvec import *
from .theory_core import *

type MinMax = tuple[int, int]


def minmax(term: BTerm) -> MinMax:
    """Determine the min-max range of a newly-constructed bitvector."""
    mask = (1 << term.width) - 1
    modulus = 1 << term.width
    overlimit = 1 << (term.width - 1)
    match term:
        case BValue(a):
            return (a, a + 1)
        case Concat((BValue(0), x)):
            return (x.min, x.max)
        case BNot(x):
            return (x.max ^ mask, x.min ^ mask)
        case BAnd(x, y):
            return (0, min(x.max, y.max))
        case BOr(x, y):
            return (max(x.min, y.min), modulus)
        case Add(x, y) if x.max < overlimit and y.max < overlimit:
            return (x.min + y.min, x.max + y.max)
        case Mul():
            raise NotImplementedError
        case Udiv(x, BValue(a)):
            return (x.min // a, x.max // a)
        case Urem(_, divisor):
            return (0, divisor.max)
        case Shl(x, BValue(a)):
            return (x.min << a, x.max << a)
        case Lshr(x, BValue(a)):
            return (x.min >> a, x.max >> a)
        case BXor():
            raise NotImplementedError
        case Sdiv():
            raise NotImplementedError
        case Srem():
            raise NotImplementedError
        case Smod():
            raise NotImplementedError
        case Ashr():
            raise NotImplementedError
        case SignExtend():
            raise NotImplementedError
        case Ite(_, x, y):
            return (min(x.min, y.min), max(x.max, y.max))
        case term:
            return (0, modulus)
