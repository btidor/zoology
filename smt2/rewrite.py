"""Library of term-rewriting rules, all theories."""

from __future__ import annotations

import abc
from functools import reduce
from typing import Any, cast

from .theory_bitvec import (
    Add,
    Ashr,
    BAnd,
    BitVector,
    BNot,
    BOr,
    BValue,
    BXor,
    Comp,
    Concat,
    Extract,
    Ite,
    Lshr,
    Mul,
    Nand,
    Neg,
    Nor,
    Repeat,
    RotateLeft,
    RotateRight,
    Sdiv,
    Sge,
    Sgt,
    Shl,
    SignExtend,
    Sle,
    Slt,
    Smod,
    Srem,
    Sub,
    Udiv,
    Uge,
    Ugt,
    Ule,
    Ult,
    Urem,
    Xnor,
    ZeroExtend,
)
from .theory_core import (
    And,
    CIte,
    Constraint,
    CValue,
    Distinct,
    Eq,
    Implies,
    Not,
    Or,
    Xor,
)


class RewriteMeta(abc.ABCMeta):
    """Performs term rewriting."""

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        """Construct the requested term, then rewrite it."""
        term = super(RewriteMeta, self).__call__(*args, **kwds)
        match term:
            case Constraint():
                term = constraint_reduction(term)
                term = constraint_folding(term)
                return constraint_logic(term)
            case BitVector():
                term = bitvector_reduction(term)
                term = bitvector_folding(term)
                return bitvector_logic(term)
            case _:
                raise TypeError("unknown term", term)


# Warning: when writing rules for generic operations (Eq, Distinct), make sure
# to explicitly specify the type of the arguments. Otherwise, the equivalence
# tests won't be complete!

# TODO: the two arguments to Concat may have different widths, but the
# equivalence tests assume they have the same width.


def constraint_reduction(term: Constraint) -> Constraint:
    """Rewrite fancy constraint ops into simple ones."""
    match term:
        case Implies(x, y):
            """implies: (X => Y) <=> (Y | ~X)"""
            return Or(y, Not(x))
        case Eq(Constraint() as x, Constraint() as y):
            """eq: X = Y <=> ~(X ^ Y)"""
            return Not(Xor(x, y))
        case Distinct(Constraint() as x, Constraint() as y):
            """distinct: X != Y <=> X ^ Y"""
            return Xor(x, y)
        case Distinct(BitVector() as x, BitVector() as y):
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


def constraint_folding(term: Constraint) -> Constraint:
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
            return CValue(x.sval < y.sval)
        case Sle(BValue() as x, BValue() as y):
            """sle"""
            return CValue(x.sval <= y.sval)
        case term:
            """fallthrough"""
            return term


def constraint_logic(term: Constraint) -> Constraint:
    """Perform more logical rewrites, mostly involving a constant."""
    match term:
        # Core Boolean Logic.
        case Not(Not(inner)):
            """not.not: ~(~X) <=> X"""
            return inner
        case And(CValue(True), x) | And(x, CValue(True)):
            """and.t: X & True <=> X"""
            return x
        case And(CValue(False), x) | And(x, CValue(False)):
            """and.f: X & False <=> False"""
            return CValue(False)
        case And(x, y) if x == y:
            """and.x: X & X <=> X"""
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:
            """and.ix: X & ~X <=> False"""
            return CValue(False)
        case Or(CValue(True), x) | Or(x, CValue(True)):
            """or.t: X | True <=> True"""
            return CValue(True)
        case Or(CValue(False), x) | Or(x, CValue(False)):
            """or.f: X | False <=> X"""
            return x
        case Or(x, y) if x == y:
            """or.x: X | X <=> X"""
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:
            """or.ix: X | ~X <=> True"""
            return CValue(True)
        case Xor(CValue(True), x) | Xor(x, CValue(True)):
            """xor.t: X ^ True <=> ~X"""
            return Not(x)
        case Xor(CValue(False), x) | Xor(x, CValue(False)):
            """xor.f: X ^ False <=> X"""
            return x
        case Xor(x, y) if x == y:
            """xor.x: X ^ X <=> False"""
            return CValue(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:
            """xor.ix: X ^ ~X <=> True"""
            return CValue(True)

        # Bitvector Eq.
        case Eq(BitVector() as x, BitVector() as y) if x == y:
            """beq.x: X = X <=> True"""
            return CValue(True)
        case Eq(BitVector() as x, BNot(y)) | Eq(BNot(y), BitVector() as x) if x == y:
            """beq.ix: X = ~X <=> False"""
            return CValue(False)
        case Eq(BValue(a), BNot(x)) | Eq(BNot(x), BValue(a)):
            """beq.vnot: A = ~X <=> ~A = X"""
            mask = (1 << x.width) - 1
            return Eq(BValue(mask ^ a, x.width), x)
        case (
            Eq(BValue(a), BAnd(x, BValue(b)))
            | Eq(BValue(a), BAnd(BValue(b), x))
            | Eq(BAnd(x, BValue(b)), BValue(a))
            | Eq(BAnd(BValue(b), x), BValue(a))
        ) if a & (b ^ ((1 << x.width) - 1)) != 0:
            """beq.vand"""
            return CValue(False)
        case (
            Eq(BValue(a), BOr(x, BValue(b)))
            | Eq(BValue(a), BOr(BValue(b), x))
            | Eq(BOr(x, BValue(b)), BValue(a))
            | Eq(BOr(BValue(b), x), BValue(a))
        ) if (a ^ ((1 << x.width) - 1)) & b != 0:
            """beq.vor"""
            return CValue(False)
        case (
            Eq(BValue(a), BXor(x, BValue(b)))
            | Eq(BValue(a), BXor(BValue(b), x))
            | Eq(BXor(x, BValue(b)), BValue(a))
            | Eq(BXor(BValue(b), x), BValue(a))
        ):
            """bveq.vxor: A = X ^ B <=> A ^ B = X"""
            return Eq(BValue(a ^ b, x.width), x)
        case (
            Eq(BValue(a), Add(x, BValue(b)))
            | Eq(BValue(a), Add(BValue(b), x))
            | Eq(Add(x, BValue(b)), BValue(a))
            | Eq(Add(BValue(b), x), BValue(a))
        ):
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
        case term:
            """fallthrough"""
            return term


def bitvector_reduction(term: BitVector) -> BitVector:
    """Rewrite fancy bitvector ops into simple ones."""
    match term:
        case Neg(x):
            """neg: negate(X) <=> ~X + 1"""
            return Add(BNot(x), BValue(1, term.width))
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


def bitvector_folding(term: BitVector) -> BitVector:
    """Perform constant folding on the given bitvector."""
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Concat(terms) if all(isinstance(t, BValue) for t in terms):
            s = reduce(lambda p, q: (p << q.width) | cast(BValue, q).value, terms, 0)
            return BValue(s, term.width)
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
            return BValue(x.sval // y.sval, width)
        case Srem(BValue() as x, BValue(b) as y) if b != 0:
            """srem"""
            r = abs(x.sval % y.sval)
            r = r if x.sval >= 0 else -r
            return BValue(r, width)
        case Smod(BValue() as x, BValue(b) as y) if b != 0:
            """smod"""
            return BValue(x.sval % y.sval, width)
        case Ashr(BValue() as x, BValue(b)):
            """ashr"""
            return BValue(x.sval >> b, width)
        case Repeat(_, BValue(a)):
            """repeat"""
            raise NotImplementedError
        case ZeroExtend(_, BValue(a)):
            """zero_extend"""
            return BValue(a, width)
        case SignExtend(_, BValue() as x):
            """sign_extend"""
            return BValue(x.sval, width)
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


def bitvector_logic(term: BitVector) -> BitVector:
    """Perform more logical rewrites, mostly involving a constant."""
    width = term.width
    mask = (1 << width) - 1
    match term:
        # Boolean Logic.
        case BNot(BNot(inner)):
            """bnot.bnot: ~(~X) <=> X"""
            return inner
        case BAnd(BValue(0), x) | BAnd(x, BValue(0)):
            """band.f: X & 0000 <=> 0000"""
            return BValue(0, width)
        case BAnd(BValue(m), x) | BAnd(x, BValue(m)) if m == mask:
            """band.t: X & 1111 <=> X"""
            return x
        case BAnd(x, y) if x == y:
            """band.x: X & X <=> X"""
            return x
        case BAnd(x, BNot(y)) | BAnd(BNot(y), x) if x == y:
            """band.ix: X & ~X <=> 0000"""
            return BValue(0, width)
        case BOr(BValue(0), x) | BOr(x, BValue(0)):
            """bor.f: X | 0000 => X"""
            return x
        case BOr(BValue(m), x) | BOr(x, BValue(m)) if m == mask:
            """bor.t: X | 1111 <=> 1111"""
            return BValue(mask, width)
        case BOr(x, y) if x == y:
            """bor.x: X | X => X"""
            return x
        case BOr(x, BNot(y)) | BOr(BNot(y), x) if x == y:
            """bor.ix: X | ~X => 1111"""
            return BValue(mask, width)
        case BXor(BValue(0), x) | BXor(x, BValue(0)):
            """bxor.f: X ^ 0000 <=> X"""
            return x
        case BXor(BValue(m), x) | BXor(x, BValue(m)) if m == mask:
            """bxor.t: X ^ 1111 <=> ~X"""
            return BNot(x)
        case BXor(x, y) if x == y:
            """bxor.x: X ^ X <=> 0000"""
            return BValue(0, width)
        case BXor(x, BNot(y)) | BXor(BNot(y), x) if x == y:
            """bxor.ix: X ^ ~X <=> 1111"""
            return BValue(mask, width)

        # Arithmetic.
        case BNot(Add(x, y)):
            """bnot.add: ~(X + Y) <=> ~X + ~Y + 1"""
            return Add(Add(BNot(x), BNot(y)), BValue(1, width))
        case Add(BValue(0), x) | Add(x, BValue(0)):
            """add.z: X + 0 <=> X"""
            return x
        case Mul(BValue(0), x) | Mul(x, BValue(0)):
            """mul.z: X * 0 <=> 0"""
            return BValue(0, width)
        case Mul(BValue(1), x) | Mul(x, BValue(1)):
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
            """Smod.w: X % 1 <=> 0"""
            return BValue(0, width)

        # Concat & Shift.
        case Concat([BValue(0) as z, *rest]):
            """concat.z"""
            return ZeroExtend(z.width, Concat(tuple(rest)))
        case Concat([single]):
            """concat.w"""
            return single
        case Shl(x, BValue(val)) if val >= width:
            """shl.o"""
            return BValue(0, width)
        case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
            """shl.shl"""
            return Shl(x, BValue(a + b, width))
        case Lshr(x, BValue(val)) if val >= width:
            """lshr.o"""
            return BValue(0, width)
        case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
            """lshr.lshr"""
            return Lshr(x, BValue(a + b, width))
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
