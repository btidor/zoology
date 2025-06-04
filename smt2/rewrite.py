"""Library of term-rewriting rules, all theories."""
# ruff: noqa: F403, F405

from __future__ import annotations

import abc
from functools import reduce
from typing import Any, cast

from .theory_bitvec import *
from .theory_core import *


class RewriteMeta(abc.ABCMeta):
    """Performs term rewriting."""

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
        match term:
            case CTerm():
                term = constraint_reduction(term)
                term = constraint_folding(term)
                return constraint_logic(term)
            case BTerm():
                term = bitvector_reduction(term)
                term = bitvector_folding(term)
                term = bitvector_logic(term)
                return bitvector_yolo(term)
            case _:
                raise TypeError("unknown term", term)


# Warning: when writing rules for generic operations (Eq, Distinct), make sure
# to explicitly specify the type of the arguments. Otherwise, the equivalence
# tests won't be complete!


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
        case term:
            """fallthrough"""
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
        case term:
            """fallthrough"""
            return term


def constraint_logic(term: CTerm) -> CTerm:
    """Perform more logical rewrites, mostly involving a constant."""
    match term:
        # Core Boolean Logic.
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

        # Bitvector Eq.
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
        case Eq(BValue(a), Add(BValue(b), x)):
            """beq.vadd: A = X + B <=> A - B = X"""
            return Eq(Add(BValue(a, x.width), Neg(BValue(b, x.width))), x)

        # Bitvector Comparators.
        case Ult(x, BValue(0)):
            """ult.z: X < 0 <=> False"""
            return CValue(False)
        case Ult(BValue(0), x):
            """z.ult: 0 < X <=> X != 0"""
            return Distinct(x, BValue(0, x.width))
        case Ult(x, BValue(1)):
            """ult.w: X < 1 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ule(x, BValue(0)):
            """ule.z: X <= 0 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            """z.ule: 0 <= X <=> True"""
            return CValue(True)

        # Comparators with ZeroExtend.
        case Eq(BValue(a), ZeroExtend(_, x)) if a >= (1 << x.width):
            """eq.zv"""
            return CValue(False)
        case Ult(ZeroExtend(_, x), BValue(a)) if a >= (1 << x.width):
            """ult.zv"""
            return CValue(True)
        case Ult(BValue(a), ZeroExtend(_, x)) if a >= (1 << x.width):
            """ult.vz"""
            return CValue(False)
        case Ule(ZeroExtend(_, x), BValue(a)) if a >= (1 << x.width):
            """ule.zv"""
            return CValue(True)
        case Ule(BValue(a), ZeroExtend(_, x)) if a >= (1 << x.width):
            """ule.vz"""
            return CValue(False)
        case term:
            """fallthrough"""
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
        case term:
            """fallthrough"""
            return term


def bitvector_folding(term: BTerm) -> BTerm:
    """Perform constant folding on the given bitvector."""
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Extract(i, j, BValue(a)):
            """extract"""
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
        case Srem(BValue() as x, BValue(b) as y) if b != 0:
            """srem"""
            r = abs(x.sgnd % y.sgnd)
            r = r if x.sgnd >= 0 else -r
            return BValue(r, width)
        case Smod(BValue() as x, BValue(b) as y) if b != 0:
            """smod"""
            return BValue(x.sgnd % y.sgnd, width)
        case Ashr(BValue() as x, BValue(b)):
            """ashr"""
            return BValue(x.sgnd >> b, width)
        case Repeat(_, BValue(a)):
            """repeat"""
            raise NotImplementedError
        case ZeroExtend(_, BValue(a)):
            """zero_extend"""
            return BValue(a, width)
        case SignExtend(_, BValue() as x):
            """sign_extend"""
            return BValue(x.sgnd, width)
        case RotateLeft(_, BValue(a)):
            """rotate_left"""
            raise NotImplementedError
        case RotateRight(_, BValue(a)):
            """rotate_right"""
            raise NotImplementedError
        case Ite(CValue(True), x, _):
            """ite.t"""
            return x
        case Ite(CValue(False), _, y):
            """ite.f"""
            return y
        case term:
            """fallthrough"""
            return term


def bitvector_logic(term: BTerm) -> BTerm:
    """Perform more logical rewrites, mostly involving a constant."""
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        # Boolean Logic.
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

        # Arithmetic.
        case BNot(Add(x, y)):
            """bnot.add: ~(X + Y) <=> ~X + ~Y + 1"""
            return Add(BValue(1, width), Add(BNot(x), BNot(y)))
        case Add(BValue(0), x):
            """add.z: X + 0 <=> X"""
            return x
        case Add(x, BNot(y)) if x == y:
            """add.bnot: X + ~X <=> """
            return BValue(mask, width)
        case Add(BValue(a), Add(BValue(b), x)):
            """add.add: A + (B + X) <=> (A + B) + X"""
            return Add(BValue((a + b) % modulus, width), x)
        case Add(Add(BValue(a), x), Add(BValue(b), y)):
            """add.add: (A + X) + (B + Y) <=> (A + B) + (X + Y)"""
            return Add(BValue((a + b) % modulus, width), Add(x, y))
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

        # Shifts.
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
        case Ashr(x, BValue(0)):
            """ashr.z"""
            return x
        case ZeroExtend(0, x):
            """zext.z"""
            return x
        case ZeroExtend(i, ZeroExtend(j, x)):
            """zext.zext"""
            return ZeroExtend(i + j, x)
        case SignExtend(0, x):
            """sext.z"""
            return x
        case SignExtend(i, SignExtend(j, x)):
            """sext.sext"""
            return SignExtend(i + j, x)

        # Push boolean expressions down over ITEs.
        case Ite(_, x, y) if x == y:
            """ite.x: C ? X : X <=> X"""
            return x
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
        case term:
            """fallthrough"""
            return term


def bitvector_yolo(term: BTerm) -> BTerm:
    """
    Additional logical rewrites involving unsupported ops (i.e. Concat).

    Warning: these rewrites are *not* covered by the test suite!
    """
    match term:
        case Concat(terms) if all(isinstance(t, BValue) for t in terms):
            """concat"""
            s = reduce(lambda p, q: (p << q.width) | cast(BValue, q).value, terms, 0)
            return BValue(s, term.width)
        case Concat([BValue(0) as z, *rest]):
            """concat.z"""
            return ZeroExtend(z.width, Concat(tuple(rest)))
        case Concat([single]):
            """concat.w"""
            return single
        case Shl(Concat([x, *rest]), BValue(a)) if a >= x.width:
            """shl.concat"""
            return Concat(
                (
                    Shl(Concat(tuple(rest)), BValue(a - x.width, term.width - x.width)),
                    BValue(0, x.width),
                )
            )
        case Lshr(Concat([*rest, x]), BValue(a)) if a >= x.width:
            """lshr.concat"""
            return ZeroExtend(
                x.width,
                Lshr(Concat(tuple(rest)), BValue(a - x.width, term.width - x.width)),
            )
        case term:
            return term
