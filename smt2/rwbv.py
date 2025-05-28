"""Term-rewriting rules for the theory of bitvectors."""

from .bv import (
    Add,
    And,
    BitVector,
    Mul,
    Nand,
    Neg,
    Nor,
    Not,
    Or,
    Sub,
    Udiv,
    Urem,
    Value,
    Xnor,
    Xor,
)


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
        case _:
            return term
