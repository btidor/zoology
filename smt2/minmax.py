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
    overlimit = 1 << (term.width - 1)
    match term:
        case BValue(a):
            return (a, a)
        case Concat((BValue(0), x)):
            return (x.min, x.max)
        case BNot(x):
            return (x.max ^ mask, x.min ^ mask)
        case BAnd(x, y):
            return (0, min(x.max, y.max))
        case BOr(x, y):
            return (max(x.min, y.min), mask)
        case Add(x, y) if x.max < overlimit and y.max < overlimit:
            return (x.min + y.min, x.max + y.max)
        case Mul(x, y):
            raise NotImplementedError
        case Udiv(x, BValue(a)) if a != 0:
            return (x.min // a, x.max // a)
        case Urem(_, divisor) if divisor.min > 0:
            return (0, divisor.max)
        case Shl(x, BValue(a)):
            raise NotImplementedError
        case Lshr(x, BValue(a)):
            return (x.min >> a, x.max >> a)
        case BXor(x, y):
            raise NotImplementedError
        case Sdiv(x, y):
            raise NotImplementedError
        case Srem(x, y):
            raise NotImplementedError
        case Smod(x, y):
            raise NotImplementedError
        case Ashr(x, y):
            raise NotImplementedError
        case SignExtend(x, y):
            raise NotImplementedError
        case Ite(_, x, y):
            return (min(x.min, y.min), max(x.max, y.max))
        case _:
            return (0, mask)
