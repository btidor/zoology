"""
Library for min-max tracking of bitvector terms.

For each term, interpreted as an unsigned integer, `minmax()` propagates the
minimum and maximum value of the term across operations.
"""
# ruff: noqa: F403, F405

from __future__ import annotations

from .rewrite import (
    bitvector_folding,
    bitvector_logic_arithmetic,
    bitvector_logic_boolean,
    bitvector_logic_shifts,
    bitvector_reduction,
    constraint_folding,
    constraint_logic_bitvector,
    constraint_logic_boolean,
    constraint_reduction,
)
from .theory_array import *
from .theory_bitvec import *
from .theory_core import *

type MinMax = tuple[int, int]


def propagate_minmax(term: BTerm) -> MinMax:
    """Determine the min-max range of a newly-constructed bitvector."""
    mask = (1 << term.width) - 1
    slimit = 1 << (term.width - 1)
    match term:
        case BValue(a):
            return (a, a)
        case Concat((BValue(a), x)):
            return (x.min | (a << x.width), x.max | (a << x.width))
        case BNot(x):
            return (x.max ^ mask, x.min ^ mask)
        case BAnd(x, y):
            return (0, min(x.max, y.max))
        case BOr(x, y):
            return (max(x.min, y.min), mask)
        case Add(x, y) if x.max < slimit and y.max < slimit:
            return (x.min + y.min, x.max + y.max)
        case Add(BValue() as x, y) if x.sgnd < 0 and y.min + x.sgnd > 0:
            return (y.min + x.sgnd, y.max + x.sgnd)
        case Mul(BValue(a), y) if a * y.max <= mask:
            return (a * y.min, a * y.max)
        case Udiv(x, BValue(a)) if a != 0:
            return (x.min // a, x.max // a)
        case Urem(_, y) if y.min > 0:
            return (0, y.max - 1)
        case Shl(x, BValue(a)) if a < term.width and (x.max << a) <= mask:
            return (min(x.min << a, mask), min(x.max << a, mask))
        case Shl(x, BValue(a)) if a < term.width:
            return (0, min(x.max << a, mask))
        case Lshr(x, BValue(a)):
            return (x.min >> a, x.max >> a)
        case Sdiv(x, BValue(a)) if x.max < slimit and a < slimit and a != 0:
            return (x.min // a, x.max // a)
        case Srem(x, y) if x.max < slimit and y.min > 0 and y.max < slimit:
            return (0, y.max - 1)
        case Smod(_, y) if y.min > 0 and y.max < slimit:
            return (0, y.max - 1)
        case Ashr(x, BValue(a)) if x.max < slimit:
            return (x.min >> a, x.max >> a)
        case SignExtend(_i, x) if x.max < (1 << (x.width - 1)):
            return (x.min, x.max)
        case Ite(_, x, y):
            return (min(x.min, y.min), max(x.max, y.max))
        case _:
            return (0, mask)


def constraint_minmax(term: CTerm) -> CTerm:
    """Rewrite comparison operators using min-max information."""
    match term:
        case Eq(BTerm() as x, BTerm() as y) if x.max < y.min:
            """beq.lt"""
            return CValue(False)
        case Eq(BTerm() as x, BTerm() as y) if y.max < x.min:
            """beq.gt"""
            return CValue(False)
        case Ult(x, y) if x.max < y.min:
            """ult.t"""
            return CValue(True)
        case Ult(x, y) if y.max <= x.min:
            """ult.f"""
            return CValue(False)
        case Ule(x, y) if x.max <= y.min:
            """ule.t"""
            return CValue(True)
        case Ule(x, y) if y.max < x.min:
            """ule.f"""
            return CValue(False)
        case Slt(x, y) if x.max < y.min and y.max < (1 << (y.width - 1)):
            """slt.pt"""
            return CValue(True)
        case Slt(x, y) if y.max <= x.min and x.max < (1 << (x.width - 1)):
            """slt.pf"""
            return CValue(False)
        case Slt(x, y) if y.max < (1 << (y.width - 1)) and x.min >= (
            1 << (x.width - 1)
        ):
            """slt.np"""
            return CValue(True)
        case Slt(x, y) if x.max < (1 << (x.width - 1)) and y.min >= (
            1 << (y.width - 1)
        ):
            """slt.pn"""
            return CValue(False)
        case Slt(x, y) if x.max < y.min and x.min >= (1 << (x.width - 1)):
            """slt.nt"""
            return CValue(True)
        case Slt(x, y) if y.max <= x.min and y.min >= (1 << (y.width - 1)):
            """slt.nf"""
            return CValue(False)
        case Sle(x, y) if x.max <= y.min and y.max < (1 << (y.width - 1)):
            """sle.pt"""
            return CValue(True)
        case Sle(x, y) if y.max < x.min and x.max < (1 << (x.width - 1)):
            """sle.pf"""
            return CValue(False)
        case Sle(x, y) if y.max < (1 << (y.width - 1)) and x.min >= (
            1 << (x.width - 1)
        ):
            """sle.np"""
            return CValue(True)
        case Sle(x, y) if x.max < (1 << (x.width - 1)) and y.min >= (
            1 << (y.width - 1)
        ):
            """sle.pn"""
            return CValue(False)
        case Sle(x, y) if x.max <= y.min and x.min >= (1 << (x.width - 1)):
            """sle.nt"""
            return CValue(True)
        case Sle(x, y) if y.max < x.min and y.min >= (1 << (y.width - 1)):
            """sle.nf"""
            return CValue(False)
        case _:
            return term


class RewriteMeta(abc.ABCMeta):
    """Performs term rewriting and min-max propagation."""

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        """Construct the requested term, then rewrite it."""
        assert issubclass(self, BaseTerm)
        if issubclass(self, Select):
            # Custom logic for arrays.
            return self.simplify(*args, **kwds, call=super(RewriteMeta, self).__call__)
        if self.commutative:
            # Swap Values to right-hand side, Nots to left-hand side.
            match args:
                case (x, CValue() as y) if not isinstance(x, CValue):
                    args = (y, x)
                case (Not() as x, y) if not isinstance(y, Not):
                    args = (y, x)
                case (x, BValue() as y) if not isinstance(x, BValue):
                    args = (y, x)
                case (BNot() as x, y) if not isinstance(y, BNot):
                    args = (y, x)
                case _:
                    pass
        term = super(RewriteMeta, self).__call__(*args, **kwds)
        match term:
            case CTerm():
                term = constraint_reduction(term)
                term = constraint_folding(term)
                term = constraint_logic_boolean(term)
                term = constraint_logic_bitvector(term)
                term = constraint_minmax(term)
            case BTerm():
                term = bitvector_reduction(term)
                term = bitvector_folding(term)
                term = bitvector_logic_boolean(term)
                term = bitvector_logic_arithmetic(term)
                term = bitvector_logic_shifts(term)
                min, max = propagate_minmax(term)
                object.__setattr__(term, "min", min)
                object.__setattr__(term, "max", max)
            case _:
                raise TypeError("unknown term", term)
        return term
