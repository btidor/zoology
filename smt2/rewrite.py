"""Library of term-rewriting rules, all theories."""
# ruff: noqa: F403, F405

from __future__ import annotations

import copy

from line_profiler import profile

from .theory_array import *
from .theory_bitvec import *
from .theory_core import *


class RewriteMeta(abc.ABCMeta):
    """Performs term rewriting."""

    _cache = dict[Any, Any]()

    @profile
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        """Construct the requested term, then rewrite it."""
        assert issubclass(self, BaseTerm)
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
        term = term.rewrite()
        term.bzla()  # populate cache to avoid deep recursion
        return term


class CacheMeta(RewriteMeta):
    """Term-caching metaclass."""

    _cache = dict[tuple[Any, ...], Any]()

    @profile
    def __call__(self, *args: Any) -> Any:
        """Return the given term, using the cache. Skip rewrites."""
        if args not in self._cache:
            self._cache[args] = super().__call__(*args)
        return self._cache[args]


def constraint_reduction(term: CTerm) -> CTerm:
    """Rewrite fancy constraint ops into simple ones."""
    match term:
        case Implies(x, y):
            """implies: (X => Y) <=> (Y | ~X)"""
            return Or(y, Not(x))
        case Eq(CTerm() as x, CTerm() as y):
            """eq: X = Y <=> ~(X ^ Y)"""
            return Not(Xor(x, y))
        case Distinct(CTerm() as x, CTerm() as y):
            """distinct: X != Y <=> X ^ Y"""
            return Xor(x, y)
        case Distinct(BTerm() as x, BTerm() as y):
            """distinct: X != Y <=> ~(X = Y)"""
            return Not(Eq(x, y))
        case CIte(c, x, y):
            """cite: ite(c, x, y) <=> (C & X) | (~C & Y)"""
            return Or(And(c, x), And(Not(c), y))
        case Ugt(x, y):
            """ugt: X > Y <=> Y < X"""
            return Ult(y, x)
        case Uge(x, y):
            """uge: X >= Y <=> Y <= X"""
            return Ule(y, x)
        case Sgt(x, y):
            """sgt: X > Y <=> Y < X"""
            return Slt(y, x)
        case Sge(x, y):
            """sge: X >= Y <=> Y <= X"""
            return Sle(y, x)
        case _:
            return term


def constraint_folding(term: CTerm) -> CTerm:
    """Perform constant folding on the given constraint."""
    match term:
        case Not(CValue(a)):
            """not"""
            return CValue(not a)
        case And(CValue(a), CValue(b)):
            """and"""
            return CValue(a and b)
        case Or(CValue(a), CValue(b)):
            """or"""
            return CValue(a or b)
        case Xor(CValue(a), CValue(b)):
            """xor"""
            return CValue(a != b)
        case Eq(BValue(a), BValue(b)):
            """eq"""
            return CValue(a == b)
        case Ult(BValue(a), BValue(b)):
            """ult"""
            return CValue(a < b)
        case Ule(BValue(a), BValue(b)):
            """ule"""
            return CValue(a <= b)
        case Slt(BValue() as x, BValue() as y):
            """slt"""
            return CValue(x.sgnd < y.sgnd)
        case Sle(BValue() as x, BValue() as y):
            """sle"""
            return CValue(x.sgnd <= y.sgnd)
        case _:
            return term


def constraint_logic_boolean(term: CTerm) -> CTerm:
    """Perform logical rewrites involving booleans."""
    match term:
        case Not(Not(inner)):
            """not.not: ~(~X) <=> X"""
            return inner
        case And(CValue(True), x):
            """and.t: X & True <=> X"""
            return x
        case And(CValue(False), x):
            """and.f: X & False <=> False"""
            return CValue(False)
        case And(x, y) if x == y:
            """and.x: X & X <=> X"""
            return x
        case And(x, Not(y)) if x == y:
            """and.ix: X & ~X <=> False"""
            return CValue(False)
        case Not(And(x, y)):
            """not.and: ~(X & Y) <=> ~X | ~Y"""
            return Or(Not(x), Not(y))
        case Or(CValue(True), x):
            """or.t: X | True <=> True"""
            return CValue(True)
        case Or(CValue(False), x):
            """or.f: X | False <=> X"""
            return x
        case Or(x, y) if x == y:
            """or.x: X | X <=> X"""
            return x
        case Or(x, Not(y)) if x == y:
            """or.ix: X | ~X <=> True"""
            return CValue(True)
        case Not(Or(x, y)):
            """not.or: ~(X | Y) <=> ~X & ~Y"""
            return And(Not(x), Not(y))
        case Xor(CValue(True), x):
            """xor.t: X ^ True <=> ~X"""
            return Not(x)
        case Xor(CValue(False), x):
            """xor.f: X ^ False <=> X"""
            return x
        case Xor(x, y) if x == y:
            """xor.x: X ^ X <=> False"""
            return CValue(False)
        case Xor(x, Not(y)) if x == y:
            """xor.ix: X ^ ~X <=> True"""
            return CValue(True)
        case _:
            return term


def constraint_logic_bitvector(term: CTerm) -> CTerm:
    """Perform logical rewrites involving bitvector comparators."""
    match term:
        case Eq(BTerm() as x, BTerm() as y) if x == y:
            """beq.x: X = X <=> True"""
            return CValue(True)
        case Eq(BTerm() as x, BNot(y)) if x == y:
            """beq.ix: X = ~X <=> False"""
            return CValue(False)
        case Eq(BValue(a), BNot(x)):
            """beq.vnot: A = ~X <=> ~A = X"""
            mask = (1 << x.width) - 1
            return Eq(BValue(mask ^ a, x.width), x)
        case Eq(BValue(a), BAnd(BValue(b), x)) if a & (b ^ ((1 << x.width) - 1)) != 0:
            """beq.vand"""
            return CValue(False)
        case Eq(BValue(a), BOr(BValue(b), x)) if (a ^ ((1 << x.width) - 1)) & b != 0:
            """beq.vor"""
            return CValue(False)
        case Eq(BValue(a), BXor(BValue(b), x)):
            """bveq.vxor: A = X ^ B <=> A ^ B = X"""
            return Eq(BValue(a ^ b, x.width), x)
        case Eq(BValue(a), Add(x, BNot(y))) if a == (1 << x.width) - 1:
            """beq.arith: -1 = A + ~B <=> A = B"""
            # This rewrite was discovered in test_universal.py::test_sudoku and
            # reduces the time for that test case by 48%.
            return Eq(x, y)
        case Eq(BValue(a), Add(BValue(b), x)):
            """beq.vadd: A = X + B <=> A - B = X"""
            return Eq(BValue((a - b) % (1 << x.width), x.width), x)
        case Eq(BTerm() as z, Ite(c, x, y)) if z == x:
            """beq.xite"""
            return Or(c, Eq(z, y))
        case Eq(BTerm() as z, Ite(c, x, y)) if z == y:
            """beq.itex"""
            return Or(Not(c), Eq(z, x))
        case Eq(BValue(a) as v, Ite(c, BValue(p), y)) if a != p:
            """beq.vite"""
            return And(Not(c), Eq(v, y))
        case Eq(BValue(a) as v, Ite(c, x, BValue(q))) if a != q:
            """beq.itev"""
            return And(c, Eq(v, x))
        case Eq(BValue(a) as x, Concat([BValue(b) as y, *rest])) if len(rest) > 0:
            """beq.vcat"""
            rwidth = x.width - y.width
            return And(
                CValue(a >> rwidth == b),
                Eq(BValue(a & ((1 << rwidth) - 1), rwidth), Concat((*rest,))),
            )
        case Ult(x, BValue(0)):
            """ult.z: X < 0 <=> False"""
            return CValue(False)
        case Ule(x, BValue(0)):
            """ule.z: X <= 0 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ult(BValue(0), x):
            """z.ult: 0 < X <=> X != 0"""
            return Distinct(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            """z.ule: 0 <= X <=> True"""
            return CValue(True)
        case Ult(x, BValue(1)):
            """ult.w: X < 1 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ult(x, y) if x == y:
            """ult.x: X < X <=> False"""
            return CValue(False)
        case Ule(x, y) if x == y:
            """ule.x: X <= X <=> True"""
            return CValue(True)
        case Not(Ult(x, y)):
            """not.ult: ~(X < Y) <=> Y <= X"""
            return Ule(y, x)
        case Not(Ule(x, y)):
            """not.ule: ~(X <= Y) <=> Y < X"""
            return Ult(y, x)
        case Not(Slt(x, y)):
            """not.slt: ~(X < Y) <=> Y <= X"""
            return Sle(y, x)
        case Not(Sle(x, y)):
            """not.sle: ~(X <= Y) <=> Y < X"""
            return Slt(y, x)

        # Compare-and-Concat
        case Ult(BValue(a), Concat([BValue(b) as x, *rest]) as c) if (
            b == (a >> (c.width - x.width)) and len(rest) > 0
        ):
            """ult.vcat"""
            rwidth = c.width - x.width
            return Ult(BValue(a & ((1 << rwidth) - 1), rwidth), Concat((*rest,)))
        case Ult(Concat([BValue(b) as x, *rest]) as c, BValue(a)) if (
            b == (a >> (c.width - x.width)) and len(rest) > 0
        ):
            """ult.catv"""
            rwidth = c.width - x.width
            return Ult(Concat((*rest,)), BValue(a & ((1 << rwidth) - 1), rwidth))
        case Ule(BValue(a), Concat([BValue(b) as x, *rest]) as c) if (
            b == (a >> (c.width - x.width)) and len(rest) > 0
        ):
            """ule.vcat"""
            rwidth = c.width - x.width
            return Ule(BValue(a & ((1 << rwidth) - 1), rwidth), Concat((*rest,)))
        case Ule(Concat([BValue(b) as x, *rest]) as c, BValue(a)) if (
            b == (a >> (c.width - x.width)) and len(rest) > 0
        ):
            """ule.catv"""
            rwidth = c.width - x.width
            return Ule(Concat((*rest,)), BValue(a & ((1 << rwidth) - 1), rwidth))

        # Compare-and-Add
        case Ult(Add(BValue(a), x), BValue(b)) if a <= b and x.max < (1 << x.width) - a:
            """ult.add: X + A < B <=> X < (B - A)"""
            return Ult(x, BValue(b - a, x.width))
        case Ult(BValue(b), Add(BValue(a), x)) if a <= b and x.max < (1 << x.width) - a:
            """ult.add: B < X + A <=> (B - A) < X"""
            return Ult(BValue(b - a, x.width), x)
        case Ult(Add(BValue(a), x), BValue(b)) if a > b and x.min >= (1 << x.width) - a:
            """ult.add: X + A < B <=> X < (B - A)"""  # Thanks, GPT-5!
            return Ult(x, BValue(b - a + (1 << x.width), x.width))
        case Ult(BValue(b), Add(BValue(a), x)) if a > b and x.min >= (1 << x.width) - a:
            """ult.add: B < X + A <=> (B - A) < X"""
            return Ult(BValue(b - a + (1 << x.width), x.width), x)
        case Ule(Add(BValue(a), x), BValue(b)) if a <= b and x.max < (1 << x.width) - a:
            """ule.add: X + A < B <=> X < (B - A)"""
            return Ule(x, BValue(b - a, x.width))
        case Ule(BValue(b), Add(BValue(a), x)) if a <= b and x.max < (1 << x.width) - a:
            """ule.add: B < X + A <=> (B - A) < X"""
            return Ule(BValue(b - a, x.width), x)
        case Ule(Add(BValue(a), x), BValue(b)) if a > b and x.min >= (1 << x.width) - a:
            """ule.add: X + A < B <=> X < (B - A)"""
            return Ule(x, BValue(b - a + (1 << x.width), x.width))
        case Ule(BValue(b), Add(BValue(a), x)) if a > b and x.min >= (1 << x.width) - a:
            """ule.add: B < X + A <=> (B - A) < X"""
            return Ule(BValue(b - a + (1 << x.width), x.width), x)
        case Slt(Add(BValue(a) as p, x), BValue(b) as q) if (
            0 <= p.sgnd and p.sgnd <= q.sgnd and x.max < (1 << (x.width - 1)) - q.sgnd
        ):
            """slt.add: X + A < B <=> X < (B- A)"""
            return Slt(x, BValue(b - a, x.width))
        case Slt(BValue(b) as q, Add(BValue(a) as p, x)) if (
            0 <= p.sgnd and p.sgnd <= q.sgnd and x.max < (1 << (x.width - 1)) - q.sgnd
        ):
            """slt.add B < X + A <=> (B - A) < X"""
            return Slt(BValue(b - a, x.width), x)
        case Slt(Add(BValue(a) as p, x), BValue(b)) if (
            p.sgnd < 0
            and -p.sgnd < (1 << x.width - 1)
            and b - p.sgnd < (1 << x.width - 1)
            and x.max < (1 << x.width - 2)
        ):
            """slt.add: X + A < B <=> X < (B - A)"""
            return Slt(x, BValue(b - p.sgnd, x.width))
        case Slt(BValue(b), Add(BValue(a) as p, x)) if (
            p.sgnd < 0
            and -p.sgnd < (1 << x.width - 1)
            and b - p.sgnd < (1 << x.width - 1)
            and x.max < (1 << x.width - 2)
        ):
            """slt.add: X + A < B <=> X < (B - A)"""
            return Slt(BValue(b - p.sgnd, x.width), x)
        case Sle(Add(BValue(a) as p, x), BValue(b) as q) if (
            0 <= p.sgnd and p.sgnd <= q.sgnd and x.max < (1 << (x.width - 1)) - q.sgnd
        ):
            """sle.add: X + A < B <=> X < (B- A)"""
            return Sle(x, BValue(b - a, x.width))
        case Sle(BValue(b) as q, Add(BValue(a) as p, x)) if (
            0 <= p.sgnd and p.sgnd <= q.sgnd and x.max < (1 << (x.width - 1)) - q.sgnd
        ):
            """sle.add B < X + A <=> (B - A) < X"""
            return Sle(BValue(b - a, x.width), x)
        case Sle(Add(BValue(a) as p, x), BValue(b)) if (
            p.sgnd < 0
            and -p.sgnd < (1 << x.width - 1)
            and b - p.sgnd < (1 << x.width - 1)
            and x.max < (1 << x.width - 2)
        ):
            """sle.add: X + A < B <=> X < (B - A)"""
            return Sle(x, BValue(b - p.sgnd, x.width))
        case Sle(BValue(b), Add(BValue(a) as p, x)) if (
            p.sgnd < 0
            and -p.sgnd < (1 << x.width - 1)
            and b - p.sgnd < (1 << x.width - 1)
            and x.max < (1 << x.width - 2)
        ):
            """sle.add: X + A < B <=> X < (B - A)"""
            return Sle(BValue(b - p.sgnd, x.width), x)
        case Ult(Add(BValue(a), x), y) if x == y and a > 0:
            """ult.add*"""
            return Ule(BValue((1 << x.width) - a, x.width), x)
        case Ult(x, Add(BValue(a), y)) if x == y and a > 0:
            """ult.add*"""
            return Ult(x, BValue((1 << x.width) - a, x.width))

        case _:
            return term


def bitvector_reduction(term: BTerm) -> BTerm:
    """Rewrite fancy bitvector ops into simple ones."""
    match term:
        case Neg(x):
            """neg: negate(X) <=> ~X + 1"""
            return Add(BValue(1, term.width), BNot(x))
        case Nand(x, y):
            """nand: X nand Y <=> ~(X & Y)"""
            return BNot(BAnd(x, y))
        case Nor(x, y):
            """nor: X nor Y <=> ~(X | Y)"""
            return BNot(BOr(x, y))
        case Xnor(x, y):
            """xnor: X xnor Y <=> ~(X ^ Y)"""
            return BNot(BXor(x, y))
        case Comp(x, y):
            """comp: comp(x, y) <=> X = Y ? 1 : 0"""
            return Ite(Eq(x, y), BValue(1, 1), BValue(0, 1))
        case Sub(x, y):
            """sub: X - Y <=> X + ~Y + 1"""
            return Add(Add(x, BNot(y)), BValue(1, term.width))
        case Repeat(1, x):
            """repeat.w"""
            return x
        case Repeat(i, x) if i > 1:
            """repeat.n"""
            return Concat((x, Repeat(i - 1, x)))
        case ZeroExtend(0, x):
            """zext.z"""
            return x
        case ZeroExtend(i, x) if i > 0:
            """zext.n"""
            return Concat((BValue(0, i), x))
        case RotateLeft(i, x) if i % term.width == 0:
            """rotl.z"""
            return x
        case RotateLeft(i, x) if i % term.width != 0:
            """rotl.n"""
            i = i % term.width
            return Concat(
                (
                    Extract(term.width - i - 1, 0, x),
                    Extract(term.width - 1, term.width - i, x),
                )
            )
        case RotateRight(i, x) if i % term.width == 0:
            """rotr.z"""
            return x
        case RotateRight(i, x) if i % term.width != 0:
            """rotr.n"""
            i = i % term.width
            return Concat((Extract(i - 1, 0, x), Extract(term.width - 1, i, x)))
        case _:
            return term


def bitvector_folding(term: BTerm) -> BTerm:
    """Perform constant folding on the given bitvector."""
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Concat([single]):
            """cat.w"""
            return single
        case Concat([BValue(a) as x, BValue(b) as y, *rest]):
            """cat.n"""
            return Concat((BValue(a << y.width | b, x.width + y.width), *rest))
        case Concat([*rest, BValue(a) as x, BValue(b) as y]):
            """n.cat"""
            return Concat((*rest, BValue(a << y.width | b, x.width + y.width)))
        case Extract(i, j, BValue(a)):
            """xtr"""
            return BValue((a >> j) & ((1 << (i - j + 1)) - 1), i - j + 1)
        case BNot(BValue(a)):
            """bnot"""
            return BValue(a ^ mask, width)
        case BAnd(BValue(a), BValue(b)):
            """band"""
            return BValue(a & b, width)
        case BOr(BValue(a), BValue(b)):
            """bor"""
            return BValue(a | b, width)
        case BXor(BValue(a), BValue(b)):
            """bxor"""
            return BValue(a ^ b, width)
        case Add(BValue(a), BValue(b)):
            """add"""
            return BValue((a + b) % modulus, width)
        case Mul(BValue(a), BValue(b)):
            """mul"""
            return BValue((a * b) % modulus, width)
        case Udiv(BValue(a), BValue(b)) if b != 0:
            """udiv"""
            return BValue(a // b, width)
        case Urem(BValue(a), BValue(b)) if b != 0:
            """urem"""
            return BValue((a % b) % modulus, width)
        case Shl(BValue(a), BValue(b)):
            """shl"""
            return BValue((a << b) % modulus, width)
        case Lshr(BValue(a), BValue(b)):
            """lshr"""
            return BValue((a >> b) % modulus, width)
        case Sdiv(BValue() as x, BValue(b) as y) if b != 0:
            """sdiv"""
            return BValue(x.sgnd // y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd > 0:
            """srem"""
            return BValue(x.sgnd % y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd < 0:
            """srem"""
            return BValue(x.sgnd % -y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd > 0:
            """srem"""
            return BValue(-(-x.sgnd % y.sgnd), width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd < 0:
            """srem"""
            return BValue(x.sgnd % y.sgnd, width)
        case Smod(BValue() as x, BValue(b) as y) if b != 0:
            """smod"""
            return BValue(x.sgnd % y.sgnd, width)
        case Ashr(BValue() as x, BValue(b)) if x.sgnd >= 0:
            """ashr"""
            return BValue(x.sgnd >> b, width)
        case Ashr(BValue(a) as x, BValue(b)) if x.sgnd < 0:
            """ashr"""
            return BValue(((a ^ mask) >> b) ^ mask, width)
        case SignExtend(_i, BValue() as x):
            """sext"""
            return BValue(x.sgnd, width)
        case Ite(CValue(True), x, _y):
            """ite.t"""
            return x
        case Ite(CValue(False), _x, y):
            """ite.f"""
            return y
        case _:
            return term


def bitvector_logic_boolean(term: BTerm) -> BTerm:
    """Perform logical rewrites involving boolean ops on bitvectors."""
    width = term.width
    mask = (1 << width) - 1
    match term:
        case BNot(BNot(inner)):
            """bnot.bnot: ~(~X) <=> X"""
            return inner
        case BAnd(BValue(0), x):
            """band.f: X & 0000 <=> 0000"""
            return BValue(0, width)
        case BAnd(BValue(m), x) if m == mask:
            """band.t: X & 1111 <=> X"""
            return x
        case BAnd(x, y) if x == y:
            """band.x: X & X <=> X"""
            return x
        case BAnd(x, BNot(y)) if x == y:
            """band.ix: X & ~X <=> 0000"""
            return BValue(0, width)
        case BAnd(BValue(a), BAnd(BValue(b), x)):
            """band.band: A & (B & X) <=> (A & B) & X"""
            return BAnd(BValue(a & b, width), x)
        case BOr(BValue(0), x):
            """bor.f: X | 0000 => X"""
            return x
        case BOr(BValue(m), x) if m == mask:
            """bor.t: X | 1111 <=> 1111"""
            return BValue(mask, width)
        case BOr(x, y) if x == y:
            """bor.x: X | X => X"""
            return x
        case BOr(x, BNot(y)) if x == y:
            """bor.ix: X | ~X => 1111"""
            return BValue(mask, width)
        case BOr(BValue(a), BOr(BValue(b), x)):
            """bor.bor: A | (B | X) <=> (A | B) | X"""
            return BOr(BValue(a | b, width), x)
        case BXor(BValue(0), x):
            """bxor.f: X ^ 0000 <=> X"""
            return x
        case BXor(BValue(m), x) if m == mask:
            """bxor.t: X ^ 1111 <=> ~X"""
            return BNot(x)
        case BXor(x, y) if x == y:
            """bxor.x: X ^ X <=> 0000"""
            return BValue(0, width)
        case BXor(x, BNot(y)) if x == y:
            """bxor.ix: X ^ ~X <=> 1111"""
            return BValue(mask, width)
        case BXor(BValue(a), BXor(BValue(b), x)):
            """bxor.bxor: A ^ (B ^ X) <=> (A ^ B) ^ X"""
            return BXor(BValue(a ^ b, width), x)
        case _:
            return term


def bitvector_logic_arithmetic(term: BTerm) -> BTerm:
    """Perform arithmetic rewrites on bitvectors."""
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case BNot(Add(x, y)):
            """bnot.add: ~(X + Y) <=> ~X + ~Y + 1"""
            return Add(BValue(1, width), Add(BNot(x), BNot(y)))
        case Add(BValue(0), x):
            """add.z: X + 0 <=> X"""
            return x
        case Add(x, BNot(y)) if x == y:
            """add.bnot: X + ~X <=> """
            return BValue(mask, width)
        case Add(x, Add(y, BNot(z))) if x == z:
            """add.bnot: X + ~X <=> """
            return Add(BValue(mask, width), y)
        case Add(BValue(a), Add(BValue(b), x)):
            """add.add: A + (B + X) <=> (A + B) + X"""
            return Add(BValue((a + b) % modulus, width), x)
        case Add(Add(BValue(a), x), Add(BValue(b), y)):
            """add.add: (A + X) + (B + Y) <=> (A + B) + (X + Y)"""
            return Add(BValue((a + b) % modulus, width), Add(x, y))
        case Add(Add(BValue(a) as z, x), y):
            """add.add: (A + X) + Y <=> A + (X + Y)"""
            return Add(z, Add(x, y))
        case Mul(BValue(0), x):
            """mul.z: X * 0 <=> 0"""
            return BValue(0, width)
        case Mul(BValue(1), x):
            """mul.w: X * 1 <=> X"""
            return x
        case Udiv(x, BValue(0)):
            """udiv.z: X // 0 <=> 1111"""
            return BValue(mask, width)
        case Udiv(x, BValue(1)):
            """udiv.w: X // 1 <=> X"""
            return x
        case Sdiv(x, BValue(0)):
            """sdiv.z: X // 0 <=> ?"""
            return Ite(Sge(x, BValue(0, width)), BValue(mask, width), BValue(1, width))
        case Sdiv(x, BValue(1)):
            """sdiv.w: X // 1 <=> X"""
            return x
        case Urem(x, BValue(0)):
            """urem.z: X % 0 <=> X"""
            return x
        case Urem(x, BValue(1)):
            """urem.w: X % 1 <=> 0"""
            return BValue(0, width)
        case Srem(x, BValue(0)):
            """srem.z: X % 0 <=> X"""
            return x
        case Srem(x, BValue(1)):
            """srem.w: X % 1 <=> 0"""
            return BValue(0, width)
        case Smod(x, BValue(0)):
            """smod.z: X % 0 <=> X"""
            return x
        case Smod(x, BValue(1)):
            """smod.w: X % 1 <=> 0"""
            return BValue(0, width)
        case _:
            return term


def bitvector_logic_shifts(term: BTerm) -> BTerm:
    """Perform logical rewrites involving bit shifts and extraction."""
    width = term.width
    mask = (1 << width) - 1
    match term:
        case Shl(x, BValue(0)):
            """shl.z"""
            return x
        case Shl(x, BValue(val)) if val >= width:
            """shl.o"""
            return BValue(0, width)
        case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
            """shl.shl"""
            return Shl(x, BValue(a + b, width))
        case Lshr(x, BValue(0)):
            """lshr.z"""
            return x
        case Lshr(x, BValue(val)) if val >= width:
            """lshr.o"""
            return BValue(0, width)
        case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
            """lshr.lshr"""
            return Lshr(x, BValue(a + b, width))
        case Lshr(BAnd(x, y), z):
            """lshr.band"""
            return BAnd(Lshr(x, z), Lshr(y, z))
        case Lshr(BOr(x, y), z):
            """lshr.bor"""
            return BOr(Lshr(x, z), Lshr(y, z))
        case Lshr(BXor(x, y), z):
            """lshr.bxor"""
            return BXor(Lshr(x, z), Lshr(y, z))
        case Lshr(Ite(c, x, y), z):
            """lshr.ite"""
            return Ite(c, Lshr(x, z), Lshr(y, z))
        case Ashr(x, BValue(0)):
            """ashr.z"""
            return x
        case SignExtend(0, x):
            """sext.z"""
            return x
        case SignExtend(i, SignExtend(j, x)):
            """sext.sext"""
            return SignExtend(i + j, x)

        # Extract, Concat.
        case Concat([*left, Concat((*right,))]) | Concat([Concat((*left,)), *right]):
            """cat.cat"""
            return Concat((*left, *right))
        case Extract(i, j, x) if i == x.width - 1 and j == 0:
            """xtr.w"""
            return x
        case Extract(i, j, Concat([*rest, x])) if i < x.width:
            """xtr.cat"""
            return Extract(i, j, x)
        case Extract(i, j, Concat([*rest, x])) if j >= x.width:
            """xtr.cat"""
            return Extract(i - x.width, j - x.width, Concat((*rest,)))
        case Extract(i, j, Concat([x, *rest]) as c) if j >= c.width - x.width:
            """xtr.cat"""
            return Extract(i - c.width + x.width, j - c.width + x.width, x)
        case Extract(i, j, Concat([x, *rest]) as c) if i < c.width - x.width:
            """xtr.cat"""
            return Extract(i, j, Concat((*rest,)))
        case Concat([Extract(i, j, x), Extract(k, l, y), *rest]) if (
            j == k + 1 and x == y
        ):
            """cat.xtrxtr"""
            return Concat((Extract(i, l, x), *rest))
        case Concat([*rest, Extract(i, j, x), Extract(k, l, y)]) if (
            j == k + 1 and x == y
        ):
            """cat.xtrxtr"""
            return Concat((*rest, Extract(i, l, x)))
        case Concat([*rest, Extract(i, j, x), Extract(k, l, y), z]) if (
            j == k + 1 and x == y
        ):
            """cat.xtrxtr"""
            # Yes, really: Fallback uses Concat((0, ..., 0))
            return Concat((*rest, Extract(i, l, x), z))
        case Extract(i, j, Ite(c, BValue() as x, BValue() as y)):
            """xtr.ite"""
            return Ite(c, Extract(i, j, x), Extract(i, j, y))

        # ITE. Push down boolean expressions.
        case Ite(_c, x, y) if x == y:
            """ite.x: C ? X : X <=> X"""
            return x
        case Ite(Not(c), x, y):
            """ite.not: ~C ? X : Y <=> C ? Y : X"""
            return Ite(c, y, x)
        case Ite(c, Ite(d, x, y), z) if c == d:
            """ite.ite: C ? (C ? X : Y) : Z <=> C ? X : Z"""
            return Ite(c, x, z)
        case Ite(c, x, Ite(d, y, z)) if c == d:
            """ite.ite: C ? X : (C ? Y : Z) <=> C ? X : Z"""
            return Ite(c, x, z)
        case BNot(Ite(c, x, y)):
            """not.ite"""
            return Ite(c, BNot(x), BNot(y))
        case BAnd(Ite(c, x, y), z) | BAnd(z, Ite(c, x, y)):
            """and.ite"""
            return Ite(c, BAnd(x, z), BAnd(y, z))
        case BOr(Ite(c, x, y), z) | BOr(z, Ite(c, x, y)):
            """or.ite"""
            return Ite(c, BOr(x, z), BOr(y, z))
        case BXor(Ite(c, x, y), z) | BXor(z, Ite(c, x, y)):
            """xor.ite"""
            return Ite(c, BXor(x, z), BXor(y, z))

        # Pull up boolean expressions over Extract.
        case Extract(i, j, BAnd(BValue(a), x)):
            """xtr.band"""
            return BAnd(
                BValue((a >> j) & ((1 << (i - j + 1)) - 1), i - j + 1), Extract(i, j, x)
            )
        case Extract(i, j, BOr(BValue(a), x)):
            """xtr.bor"""
            return BOr(
                BValue((a >> j) & ((1 << (i - j + 1)) - 1), i - j + 1), Extract(i, j, x)
            )
        case Extract(i, j, BXor(BValue(a), x)):
            """xtr.bxor"""
            return BXor(
                BValue((a >> j) & ((1 << (i - j + 1)) - 1), i - j + 1), Extract(i, j, x)
            )

        # Push down boolean expressions over Concat. We *don't* push down BNot,
        # because this would conflict with "add.bnot" and similar rewrites.
        case BAnd(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
            """band.cat"""
            mask = (1 << x.width) - 1
            return Concat(
                (
                    BAnd(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                    BAnd(BValue(a & mask, x.width), x),
                )
            )
        case BOr(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
            """bor.cat"""
            mask = (1 << x.width) - 1
            return Concat(
                (
                    BOr(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                    BOr(BValue(a & mask, x.width), x),
                )
            )
        # Skip BXor because it triggers a bug in Z3.
        case Shl(Concat([x, *rest]), BValue(a)) if (
            a < term.width and a >= x.width and len(rest) > 0
        ):
            """shl.cat"""
            return Concat(
                (
                    Shl(Concat((*rest,)), BValue(a - x.width, term.width - x.width)),
                    BValue(0, x.width),
                )
            )
        case Lshr(Concat([*rest, x]), BValue(a)) if (
            a < term.width and a >= x.width and len(rest) > 0
        ):
            """lshr.cat"""
            return Concat(
                (
                    BValue(0, x.width),
                    Lshr(Concat((*rest,)), BValue(a - x.width, term.width - x.width)),
                )
            )
        case _:
            return term


def bitvector_yolo(term: BTerm) -> BTerm:
    """Warning: unverified rewrite rules for bitvectors."""
    match term:
        case Extract(i, j, Lshr(x, BValue(shift))) if i < x.width - shift:
            """xtr.lshr"""
            return Extract(i + shift, j + shift, x)
        case Select(AValue(d), _key):
            """sel.n"""
            return d
        case Select(Store(base, lower, upper), key):
            """sel.sto"""
            for k, v in reversed(upper):
                match Eq(k, key):
                    case CValue(True):  # pyright: ignore[reportUnnecessaryComparison]
                        return v
                    case CValue(False):  # pyright: ignore[reportUnnecessaryComparison]
                        continue
                    case _:
                        return term
            match key:
                case BValue(s):
                    if s in lower:
                        return lower[s]
                    else:
                        return Select(base, key)
                case _:
                    if not lower:
                        return Select(base, key)
                    elif upper:
                        return Select(Store(base, copy.copy(lower)), key)
                    else:
                        return term
        case _:
            return term
