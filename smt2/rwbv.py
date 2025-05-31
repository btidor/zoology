"""Term-rewriting rules for the theory of bitvectors."""

from __future__ import annotations

from typing import cast

from . import core
from .bv import (
    Add,
    And,
    BitVector,
    Ite,
    Lshr,
    Mul,
    Nand,
    Neg,
    Nor,
    Not,
    Or,
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
    Value,
    Xnor,
    Xor,
    ZeroExtend,
)
from .core import Constraint

# pyright: reportUnknownArgumentType=false
# pyright: reportUnknownVariableType=false


def rewrite_bitvector[N: int](term: BitVector[N], width: N) -> BitVector[N]:
    """Simplify the given bitvector."""
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        # Boolean Logic
        case Not(Value(val)):
            """notval"""
            return Value(mask ^ val, width)
        case Not(Not(inner)):
            """notnot: ~(~X) <=> X"""
            return inner
        case And(Value(a), Value(b)):
            """andval"""
            return Value(a & b, width)
        case And(Value(0), x) | And(x, Value(0)):
            """andzero: X & 0000 <=> 0000"""
            return Value(0, width)
        case And(Value(m), x) | And(x, Value(m)) if m == mask:
            """andone: X & 1111 <=> X"""
            return x
        case And(x, y) if x == y:
            """andself: X & X <=> X"""
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:
            """andunself: X & ~X <=> 0000"""
            return Value(0, width)
        case Or(Value(a), Value(b)):
            """orval"""
            return Value(a | b, width)
        case Or(Value(0), x) | Or(x, Value(0)):
            """orzero: X | 0000 => X"""
            return x
        case Or(Value(m), x) | Or(x, Value(m)) if m == mask:
            """orone: X | 1111 <=> 1111"""
            return Value(mask, width)
        case Or(x, y) if x == y:
            """orself: X | X => X"""
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:
            """orunself: X | ~X => 1111"""
            return Value(mask, width)
        case Xor(Value(a), Value(b)):
            """xorval"""
            return Value(a ^ b, width)
        case Xor(Value(0), x) | Xor(x, Value(0)):
            """xorzero: X ^ 0000 <=> X"""
            return x
        case Xor(Value(m), x) | Xor(x, Value(m)) if m == mask:
            """xorone: X ^ 1111 <=> ~X"""
            return Not(x)
        case Xor(x, y) if x == y:
            """xorself: X ^ X <=> 0000"""
            return Value(0, width)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:
            """xorunself: X ^ ~X <=> 1111"""
            return Value(mask, width)

        # Normalize Negated Boolean Ops
        case Nand(x, y):
            """rwnand"""
            return Not(And(x, y))
        case Nor(x, y):
            """rwnor"""
            return Not(Or(x, y))
        case Xnor(x, y):
            """rwxnor"""
            return Not(Xor(x, y))

        # Arithmetic
        case Add(Value(a), Value(b)):
            """addval"""
            return Value((a + b) % modulus, width)
        case Add(Value(0), x) | Add(x, Value(0)):
            """addzero: X + 0 <=> X"""
            return x
        case Mul(Value(a), Value(b)):
            """mulval"""
            return Value((a * b) % modulus, width)
        case Mul(Value(0), x) | Mul(x, Value(0)):
            """mulzero: X * 0 <=> 0"""
            return Value(0, width)
        case Mul(Value(1), x) | Mul(x, Value(1)):
            """mulone: X * 1 <=> X"""
            return x
        case Udiv(Value(a), Value(b)) if b != 0:
            """udivval"""
            return Value(a // b, width)
        case Udiv(x, Value(0)):
            """udivzero: X // 0 <=> 1111"""
            return Value(mask, width)
        case Udiv(x, Value(1)):
            """udivone: X // 1 <=> X"""
            return x
        case Urem(Value(a), Value(b)) if b != 0:
            """uremval"""
            return Value((a % b) % modulus, width)
        case Urem(x, Value(0)):
            """uremzero: X % 0 <=> X"""
            return x

        # Normalize Neg, Sub to arithmetic
        case Neg(x):
            """rwneg: negate(X) <=> ~X + 1"""
            return Add(Not(x), Value(1, width))
        case Sub(x, y):
            """rwsub: X - Y <=> X + ~Y + 1"""
            return Add(Add(x, Not(y)), Value(1, width))

        # Bit-shifting
        case Shl(Value(a), Value(b)):
            """shlval"""
            return Value((a << b) % modulus, width)
        case Shl(x, Value(val)) if val >= width:
            """shlover"""
            return Value(0, width)
        case Shl(Shl(x, Value(a)), Value(b)) if a < width and b < width:
            """shlshl"""
            return Shl(x, Value(a + b, width))
        case Lshr(Value(a), Value(b)):
            """lshrval"""
            return Value((a >> b) % modulus, width)
        case Lshr(x, Value(val)) if val >= width:
            """shlrover"""
            return Value(0, width)
        case Lshr(Lshr(x, Value(a)), Value(b)) if a < width and b < width:
            """lshrlshr"""
            return Lshr(x, Value(a + b, width))
        case ZeroExtend(0, x):
            """zextzero"""
            return cast(BitVector[N], x)
        case SignExtend(0, x):
            """sextzero"""
            return cast(BitVector[N], x)

        # Core Generics (Ite)
        case Ite(core.Value(True), x, y):
            """itetrue: True ? X : Y <=> X"""
            return x
        case Ite(core.Value(False), x, y):  # False ? X : Y <=> Y
            """itefalse"""
            return y
        case Ite(_, x, y) if x == y:  # C ? X : X <=> X
            """itself"""
            return x

        # Push boolean expressions down over ITEs
        case Not(Ite(c, x, y)):
            """pushnotite"""
            return Ite(c, Not(x), Not(y))
        case And(Ite(c, x, y), z) | And(z, Ite(c, x, y)):
            """pushandite"""
            return Ite(c, And(x, z), And(y, z))
        case Or(Ite(c, x, y), z) | Or(z, Ite(c, x, y)):
            """pushorite"""
            return Ite(c, Or(x, z), Or(y, z))
        case Xor(Ite(c, x, y), z) | Xor(z, Ite(c, x, y)):
            """pushxorite"""
            return Ite(c, Xor(x, z), Xor(y, z))

        case term:
            """fallthrough"""
            return term


def rewrite_mixed(term: Constraint, width: int) -> Constraint:
    """Simplify the given bitvector-containing constraint."""
    mask = (1 << width) - 1
    match term:
        # Core Generics (Eq, Distinct)
        case core.Eq(Value(a), Value(b)):
            """eqval"""
            return core.Value(a == b)
        case core.Eq(BitVector() as x, BitVector() as y) if x == y:
            """eqself: X = X <=> True"""
            return core.Value(True)
        case core.Eq(BitVector() as x, Not(y)) | core.Eq(Not(y), BitVector() as x) if (
            x == y
        ):
            """equnself: X = ~X <=> False"""
            return core.Value(False)
        case core.Distinct(BitVector() as x, BitVector() as y):
            """rwdistinct: X != Y <=> ~(X = Y)"""
            return core.Not(core.Eq(x, y))

        # Boolean Propagation over Eq
        case core.Eq(Value(a), Not(x)) | core.Eq(Not(x), Value(a)):
            """eqnotval: A = ~X <=> ~A = X"""
            return core.Eq(Value(mask ^ a, width), x)
        case (
            core.Eq(Value(a), And(x, Value(b)))
            | core.Eq(Value(a), And(Value(b), x))
            | core.Eq(And(x, Value(b)), Value(a))
            | core.Eq(And(Value(b), x), Value(a))
        ) if a & (b ^ mask) != 0:
            """eqandval"""
            return core.Value(False)
        case (
            core.Eq(Value(a), Or(x, Value(b)))
            | core.Eq(Value(a), Or(Value(b), x))
            | core.Eq(Or(x, Value(b)), Value(a))
            | core.Eq(Or(Value(b), x), Value(a))
        ) if (a ^ mask) & b != 0:
            """eqorval"""
            return core.Value(False)
        case (
            core.Eq(Value(a), Xor(x, Value(b)))
            | core.Eq(Value(a), Xor(Value(b), x))
            | core.Eq(Xor(x, Value(b)), Value(a))
            | core.Eq(Xor(Value(b), x), Value(a))
        ):
            """eqxorval: A = X ^ B <=> A ^ B = X"""
            return core.Eq(Value(a ^ b, width), x)

        # Bitvector Comparators
        case Ult(Value(a), Value(b)):
            """ultval"""
            return core.Value(a < b)
        case Ult(x, Value(0)):
            """ultzero: X < 0 <=> False"""
            return core.Value(False)
        case Ult(Value(0), x):
            """zeroult: 0 < X <=> X != 0"""
            return core.Distinct(x, Value(0, width))
        case Ult(x, Value(1)):
            """ultone: X < 1 <=> X = 0"""
            return core.Eq(x, Value(0, width))
        case Ule(Value(a), Value(b)):
            """uleval"""
            return core.Value(a <= b)
        case Ule(x, Value(0)):
            """ulezero: X <= 0 <=> X = 0"""
            return core.Eq(x, Value(0, width))
        case Ule(Value(0), x):
            """zeroule: 0 <= X <=> True"""
            return core.Value(True)

        # Normalize *gt, *ge to *lt, *le
        case Ugt(x, y):
            """rwugt"""
            return Ult[int](y, x)
        case Uge(x, y):
            """rwuge"""
            return Ule[int](y, x)
        case Sgt(x, y):
            """rwsgt"""
            return Slt[int](y, x)
        case Sge(x, y):
            """rwsge"""
            return Sle[int](y, x)

        case term:
            """fallthrough"""
            return term
