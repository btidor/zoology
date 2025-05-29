"""Term-rewriting rules for the theory of bitvectors."""

from __future__ import annotations

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
)
from .core import Constraint

# pyright: reportUnknownArgumentType=false
# pyright: reportUnknownVariableType=false


def rewrite_bitvector[N: int](term: BitVector[N], width: N) -> BitVector[N]:
    """Simplify the given bitvector."""
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        # Boolean logic
        case Not(Value(val)):
            return Value(mask ^ val, width)
        case Not(Not(inner)):  # ~(~X) <=> X
            return inner
        case And(Value(a), Value(b)):
            return Value(a & b, width)
        case And(Value(m), x) | And(x, Value(m)) if m == mask:  # X & 1111 <=> X
            return x
        case And(Value(0), x) | And(x, Value(0)):  # X & 0000 <=> 0000
            return Value(0, width)
        case And(x, y) if x == y:  # X & X <=> X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X <=> 0000
            return Value(0, width)
        case Or(Value(a), Value(b)):
            return Value(a | b, width)
        case Or(Value(m), x) | Or(x, Value(m)) if m == mask:  # X | 1111 <=> 1111
            return Value(mask, width)
        case Or(Value(0), x) | Or(x, Value(0)):  # X | 0000 => X
            return x
        case Or(x, y) if x == y:  # X | X => X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X => 1111
            return Value(mask, width)
        case Xor(Value(a), Value(b)):
            return Value(a ^ b, width)
        case Xor(Value(m), x) | Xor(x, Value(m)) if m == mask:  # X ^ 1111 <=> ~X
            return Not(x)
        case Xor(Value(0), x) | Xor(x, Value(0)):  # X ^ 0000 <=> X
            return x
        case Xor(x, y) if x == y:  # X ^ X <=> 0000
            return Value(0, width)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X <=> 1111
            return Value(mask, width)
        # Normalize negated variants
        case Nand(x, y):
            return Not(And(x, y))
        case Nor(x, y):
            return Not(Or(x, y))
        case Xnor(x, y):
            return Not(Xor(x, y))
        # Arithmetic
        case Add(Value(a), Value(b)):
            return Value((a + b) % modulus, width)
        case Add(Value(0), x) | Add(x, Value(0)):  # X + 0 <=> X
            return x
        case Mul(Value(a), Value(b)):
            return Value((a * b) % modulus, width)
        case Mul(Value(0), x) | Mul(x, Value(0)):  # X * 0 <=> 0
            return Value(0, width)
        case Mul(Value(1), x) | Mul(x, Value(1)):  # X * 1 <=> X
            return x
        case Udiv(Value(a), Value(b)) if b != 0:
            return Value(a // b, width)
        case Udiv(x, Value(0)):  # X // 0 <=> 1111
            return Value(mask, width)
        case Udiv(x, Value(1)):  # X // 1 <=> X
            return x
        case Urem(Value(a), Value(b)) if b != 0:
            return Value((a % b) % modulus, width)
        case Urem(x, Value(0)):  # X % 0 <=> X
            return x
        # Normalize Neg, Sub to arithmetic
        case Neg(x):  # negate(X) <=> ~X + 1
            return Add(Not(x), Value(1, width))
        case Sub(x, y):  # X - Y <=> X + ~Y + 1
            return Add(Add(x, Not(y)), Value(1, width))
        # Bit-shifting
        case Shl(Value(a), Value(b)):
            return Value((a << b) % modulus, width)
        case Shl(x, Value(val)) if val >= width:
            return Value(0, width)
        case Shl(Shl(x, Value(a)), Value(b)) if a < width and b < width:
            return Shl(x, Value(a + b, width))
        case Lshr(Value(a), Value(b)):
            return Value((a >> b) % modulus, width)
        case Lshr(Lshr(x, Value(a)), Value(b)) if a < width and b < width:
            return Lshr(x, Value(a + b, width))
        case Lshr(x, Value(val)) if val >= width:
            return Value(0, width)
        # Core generics
        case Ite(core.Value(True), x, y):  # True ? X : Y <=> X
            return x
        case Ite(core.Value(False), x, y):  # False ? X : Y <=> Y
            return y
        case Ite(_, x, y) if x == y:  # C ? X : X <=> X
            return x
        case other:
            return other


def rewrite_mixed(term: Constraint, width: int) -> Constraint:
    """Simplify the given bitvector-containing constraint."""
    mask = (1 << width) - 1
    match term:
        # Core generics
        case core.Eq(Value(a), Value(b)):
            return core.Value(a == b)
        case core.Eq(BitVector() as x, BitVector() as y) if x == y:
            return core.Value(True)
        case core.Eq(BitVector() as x, Not(y)) | core.Eq(Not(y), BitVector() as x) if (
            x == y
        ):
            return core.Value(False)
        case core.Eq(Value(a), Not(x)) | core.Eq(Not(x), Value(a)):
            return core.Eq(Value(mask ^ a, width), x)
        case (
            core.Eq(Value(a), And(x, Value(b)))
            | core.Eq(Value(a), And(Value(b), x))
            | core.Eq(And(x, Value(b)), Value(a))
            | core.Eq(And(Value(b), x), Value(a))
        ) if a & (b ^ mask) != 0:
            return core.Value(False)
        case (
            core.Eq(Value(a), Or(x, Value(b)))
            | core.Eq(Value(a), Or(Value(b), x))
            | core.Eq(Or(x, Value(b)), Value(a))
            | core.Eq(Or(Value(b), x), Value(a))
        ) if (a ^ mask) & b != 0:
            return core.Value(False)
        case (
            core.Eq(Value(a), Xor(x, Value(b)))
            | core.Eq(Value(a), Xor(Value(b), x))
            | core.Eq(Xor(x, Value(b)), Value(a))
            | core.Eq(Xor(Value(b), x), Value(a))
        ):
            return core.Eq(Value(a ^ b, width), x)
        case core.Distinct(BitVector() as x, BitVector() as y):
            return core.Not(core.Eq(x, y))
        # BitVector-specific comparators
        case Ult(Value(a), Value(b)):
            return core.Value(a < b)
        case Ult(x, Value(0)):  # X < 0 <=> False
            return core.Value(False)
        case Ult(Value(0), x):  # 0 < X <=> X != 0
            return core.Distinct(x, Value(0, width))
        case Ult(x, Value(1)):  # X < 1 <=> X = 0
            return core.Eq(x, Value(0, width))
        case Ule(Value(a), Value(b)):
            return core.Value(a <= b)
        case Ule(x, Value(0)):  # X <= 0 <=> X = 0
            return core.Eq(x, Value(0, width))
        case Ule(Value(0), x):  # 0 <= X <=> True
            return core.Value(True)
        case Ugt(x, y):
            return Ult[int](y, x)
        case Uge(x, y):
            return Ule[int](y, x)
        case Sgt(x, y):
            return Slt[int](y, x)
        case Sge(x, y):
            return Sle[int](y, x)
        case other:
            return other
