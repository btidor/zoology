"""Library of term-rewriting rules, all theories."""

from __future__ import annotations

import abc
from typing import Any

from .theory_bitvec import (
    Add,
    BAnd,
    BitVector,
    BNot,
    BOr,
    BValue,
    BXor,
    Concat,
    Ite,
    Lshr,
    Mul,
    Nand,
    Neg,
    Nor,
    Sge,
    Sgt,
    Shl,
    SignExtend,
    Sle,
    Slt,
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
        instance = super(RewriteMeta, self).__call__(*args, **kwds)
        match instance:
            case Constraint():
                return rewrite_constraint(instance)
            case BitVector():
                return rewrite_bitvector(instance)
            case _:
                raise NotImplementedError(instance)


def rewrite_constraint(term: Constraint) -> Constraint:
    """Simplify the given constraint."""
    match term:
        # Core Boolean Expressions.
        case Not(CValue(val)):
            """notval"""
            return CValue(not val)
        case Not(Not(inner)):
            """notnot: ~(~X) <=> X"""
            return inner
        case Implies(x, y):
            """rwimpl: (X => Y) <=> (Y | ~X)"""
            return Or(y, Not(x))
        case And(CValue(True), x) | And(x, CValue(True)):
            """andtrue: X & True <=> X"""
            return x
        case And(CValue(False), x) | And(x, CValue(False)):
            """andfalse: X & False <=> False"""
            return CValue(False)
        case And(x, y) if x == y:
            """andself: X & X <=> X"""
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:
            """andunself: X & ~X <=> False"""
            return CValue(False)
        case Or(CValue(True), x) | Or(x, CValue(True)):
            """ortrue: X | True <=> True"""
            return CValue(True)
        case Or(CValue(False), x) | Or(x, CValue(False)):
            """orfalse: X | False <=> X"""
            return x
        case Or(x, y) if x == y:
            """orself: X | X <=> X"""
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:
            """orunself: X | ~X <=> True"""
            return CValue(True)
        case Xor(CValue(True), x) | Xor(x, CValue(True)):
            """xortrue: X ^ True <=> ~X"""
            return Not(x)
        case Xor(CValue(False), x) | Xor(x, CValue(False)):
            """xorfalse: X ^ False <=> X"""
            return x
        case Xor(x, y) if x == y:
            """xorself: X ^ X <=> False"""
            return CValue(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:
            """xorunself: X ^ ~X <=> True"""
            return CValue(True)

        # Core Generics. Note: these rules should be specialized per input type,
        # or the test will not be comprehensive!
        case Eq(Constraint() as x, Constraint() as y):
            """rwceq: X = Y <=> ~(X ^ Y)"""
            return Not(Xor(x, y))
        case Eq(BitVector() as x, BitVector() as y) if x == y:
            """beqself: X = X <=> True"""
            return CValue(True)
        case Eq(BitVector() as x, BNot(y)) | Eq(BNot(y), BitVector() as x) if x == y:
            """bequnself: X = ~X <=> False"""
            return CValue(False)
        case Distinct(Constraint() as x, Constraint() as y):
            """rwcdist: X != Y <=> X ^ Y"""
            return Xor(x, y)
        case Distinct(BitVector() as x, BitVector() as y):
            """rwbdist: X != Y <=> ~(X = Y)"""
            return Not(Eq(x, y))

        # Core Ite.
        case CIte(CValue(True), x, y):
            """citetrue: True ? X : Y <=> X"""
            return x
        case CIte(CValue(False), x, y):
            """citefalse: False ? X : Y <=> Y"""
            return y
        case CIte(_, x, y) if x == y:
            """citeself: C ? X : X <=> X"""
            return x

        # Boolean Propagation over Bitvector Eq.
        case Eq(BValue(a), BNot(x)) | Eq(BNot(x), BValue(a)):
            """eqnotval: A = ~X <=> ~A = X"""
            mask = (1 << x.width) - 1
            return Eq(BValue(mask ^ a, x.width), x)
        case (
            Eq(BValue(a), BAnd(x, BValue(b)))
            | Eq(BValue(a), BAnd(BValue(b), x))
            | Eq(BAnd(x, BValue(b)), BValue(a))
            | Eq(BAnd(BValue(b), x), BValue(a))
        ) if a & (b ^ ((1 << x.width) - 1)) != 0:
            """eqandval"""
            return CValue(False)
        case (
            Eq(BValue(a), BOr(x, BValue(b)))
            | Eq(BValue(a), BOr(BValue(b), x))
            | Eq(BOr(x, BValue(b)), BValue(a))
            | Eq(BOr(BValue(b), x), BValue(a))
        ) if (a ^ (1 << x.width) - 1) & b != 0:
            """eqorval"""
            return CValue(False)
        case (
            Eq(BValue(a), BXor(x, BValue(b)))
            | Eq(BValue(a), BXor(BValue(b), x))
            | Eq(BXor(x, BValue(b)), BValue(a))
            | Eq(BXor(BValue(b), x), BValue(a))
        ):
            """eqxorval: A = X ^ B <=> A ^ B = X"""
            return Eq(BValue(a ^ b, x.width), x)
        case (
            Eq(BValue(a), Add(x, BValue(b)))
            | Eq(BValue(a), Add(BValue(b), x))
            | Eq(Add(x, BValue(b)), BValue(a))
            | Eq(Add(BValue(b), x), BValue(a))
        ):
            """eqaddval"""
            return Eq(Add(BValue(a, x.width), Neg(BValue(b, x.width))), x)

        # Bitvector Comparators.
        case Ult(BValue(a), BValue(b)):
            """ultval"""
            return CValue(a < b)
        case Ult(x, BValue(0)):
            """ultzero: X < 0 <=> False"""
            return CValue(False)
        case Ult(BValue(0), x):
            """zeroult: 0 < X <=> X != 0"""
            return Distinct(x, BValue(0, x.width))
        case Ult(x, BValue(1)):
            """ultone: X < 1 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(a), BValue(b)):
            """uleval"""
            return CValue(a <= b)
        case Ule(x, BValue(0)):
            """ulezero: X <= 0 <=> X = 0"""
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            """zeroule: 0 <= X <=> True"""
            return CValue(True)
        case Ugt(x, y):
            """rwugt"""
            return Ult(y, x)
        case Uge(x, y):
            """rwuge"""
            return Ule(y, x)
        case Sgt(x, y):
            """rwsgt"""
            return Slt(y, x)
        case Sge(x, y):
            """rwsge"""
            return Sle(y, x)
        case term:
            """fallthrough"""
            return term


def rewrite_bitvector(term: BitVector) -> BitVector:
    """Simplify the given bitvector."""
    width = term.width
    mask = (1 << term.width) - 1
    modulus = 1 << term.width
    match term:
        # Boolean Logic.
        case BNot(BValue(val)):
            """notval"""
            return BValue(mask ^ val, width)
        case BNot(BNot(inner)):
            """notnot: ~(~X) <=> X"""
            return inner
        case BAnd(BValue(a), BValue(b)):
            """andval"""
            return BValue(a & b, width)
        case BAnd(BValue(0), x) | BAnd(x, BValue(0)):
            """andzero: X & 0000 <=> 0000"""
            return BValue(0, width)
        case BAnd(BValue(m), x) | BAnd(x, BValue(m)) if m == mask:
            """andone: X & 1111 <=> X"""
            return x
        case BAnd(x, y) if x == y:
            """andself: X & X <=> X"""
            return x
        case BAnd(x, BNot(y)) | BAnd(BNot(y), x) if x == y:
            """andunself: X & ~X <=> 0000"""
            return BValue(0, width)
        case BOr(BValue(a), BValue(b)):
            """orval"""
            return BValue(a | b, width)
        case BOr(BValue(0), x) | BOr(x, BValue(0)):
            """orzero: X | 0000 => X"""
            return x
        case BOr(BValue(m), x) | BOr(x, BValue(m)) if m == mask:
            """orone: X | 1111 <=> 1111"""
            return BValue(mask, width)
        case BOr(x, y) if x == y:
            """orself: X | X => X"""
            return x
        case BOr(x, BNot(y)) | BOr(BNot(y), x) if x == y:
            """orunself: X | ~X => 1111"""
            return BValue(mask, width)
        case BXor(BValue(a), BValue(b)):
            """xorval"""
            return BValue(a ^ b, width)
        case BXor(BValue(0), x) | BXor(x, BValue(0)):
            """xorzero: X ^ 0000 <=> X"""
            return x
        case BXor(BValue(m), x) | BXor(x, BValue(m)) if m == mask:
            """xorone: X ^ 1111 <=> ~X"""
            return BNot(x)
        case BXor(x, y) if x == y:
            """xorself: X ^ X <=> 0000"""
            return BValue(0, width)
        case BXor(x, BNot(y)) | BXor(BNot(y), x) if x == y:
            """xorunself: X ^ ~X <=> 1111"""
            return BValue(mask, width)

        # Normalize Negated Boolean Ops.
        case Nand(x, y):
            """rwnand"""
            return BNot(BAnd(x, y))
        case Nor(x, y):
            """rwnor"""
            return BNot(BOr(x, y))
        case Xnor(x, y):
            """rwxnor"""
            return BNot(BXor(x, y))

        # Arithmetic.
        case Add(BValue(a), BValue(b)):
            """addval"""
            return BValue((a + b) % modulus, width)
        case Add(BValue(0), x) | Add(x, BValue(0)):
            """addzero: X + 0 <=> X"""
            return x
        case Mul(BValue(a), BValue(b)):
            """mulval"""
            return BValue((a * b) % modulus, width)
        case Mul(BValue(0), x) | Mul(x, BValue(0)):
            """mulzero: X * 0 <=> 0"""
            return BValue(0, width)
        case Mul(BValue(1), x) | Mul(x, BValue(1)):
            """mulone: X * 1 <=> X"""
            return x
        case Udiv(BValue(a), BValue(b)) if b != 0:
            """udivval"""
            return BValue(a // b, width)
        case Udiv(x, BValue(0)):
            """udivzero: X // 0 <=> 1111"""
            return BValue(mask, width)
        case Udiv(x, BValue(1)):
            """udivone: X // 1 <=> X"""
            return x
        case Urem(BValue(a), BValue(b)) if b != 0:
            """uremval"""
            return BValue((a % b) % modulus, width)
        case Urem(x, BValue(0)):
            """uremzero: X % 0 <=> X"""
            return x

        # Normalize Neg, Sub to Arithmetic.
        case Neg(x):
            """rwneg: negate(X) <=> ~X + 1"""
            return Add(BNot(x), BValue(1, width))
        case Sub(x, y):
            """rwsub: X - Y <=> X + ~Y + 1"""
            return Add(Add(x, BNot(y)), BValue(1, width))
        case BNot(Add(x, y)):
            """notadd: ~(X + Y) <=> ~X + ~Y + 1"""
            return Add(Add(BNot(x), BNot(y)), BValue(1, width))

        # Bit-shifting.
        case Shl(BValue(a), BValue(b)):
            """shlval"""
            return BValue((a << b) % modulus, width)
        case Shl(x, BValue(val)) if val >= width:
            """shlover"""
            return BValue(0, width)
        case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
            """shlshl"""
            return Shl(x, BValue(a + b, width))
        case Lshr(BValue(a), BValue(b)):
            """lshrval"""
            return BValue((a >> b) % modulus, width)
        case Lshr(x, BValue(val)) if val >= width:
            """shlrover"""
            return BValue(0, width)
        case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
            """lshrlshr"""
            return Lshr(x, BValue(a + b, width))
        case ZeroExtend(0, x):
            """zextzero"""
            return x
        case SignExtend(0, x):
            """sextzero"""
            return x
        case Concat(BValue(a) as x, BValue(b) as y):
            """concatval"""
            # Warning: SMT validation assumes that x and y are the same width.
            return BValue((a << y.width) | b, x.width + y.width)

        # Bitvector Ite.
        case Ite(CValue(True), x, y):
            """itetrue: True ? X : Y <=> X"""
            return x
        case Ite(CValue(False), x, y):
            """itefalse: False ? X : Y <=> Y"""
            return y
        case Ite(_, x, y) if x == y:
            """iteself: C ? X : X <=> X"""
            return x

        # Push boolean expressions down over ITEs.
        case BNot(Ite(c, x, y)):
            """pushnotite"""
            return Ite(c, BNot(x), BNot(y))
        case BAnd(Ite(c, x, y), z) | BAnd(z, Ite(c, x, y)):
            """pushandite"""
            return Ite(c, BAnd(x, z), BAnd(y, z))
        case BOr(Ite(c, x, y), z) | BOr(z, Ite(c, x, y)):
            """pushorite"""
            return Ite(c, BOr(x, z), BOr(y, z))
        case BXor(Ite(c, x, y), z) | BXor(z, Ite(c, x, y)):
            """pushxorite"""
            return Ite(c, BXor(x, z), BXor(y, z))
        case term:
            """fallthrough"""
            return term
