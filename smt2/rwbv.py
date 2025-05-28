"""Term-rewriting rules for the theory of bitvectors."""

from .defbv import (
    Add,
    And,
    BitVector,
    Not,
    Or,
    Value,
    Xor,
)


def rewrite_bitvector[N: int](term: BitVector[N], width: N) -> BitVector[N]:
    """Simplify the given term."""
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
        case Xor(Value(m), x) | Xor(x, Value(m)) if m == modulus:  # X ^ 1111 <=> ~X
            return Not(x)
        case Xor(Value(0), x) | Xor(x, Value(0)):  # X ^ 0000 <=> X
            return x
        case Xor(x, y) if x == y:  # X ^ X <=> 0000
            return Value(0, width)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X <=> 1111
            return Value(mask, width)
        case Add(Value(a), Value(b)):
            return Value((a + b) % modulus, width)
        case _:
            return term
