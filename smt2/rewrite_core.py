"""Term-rewriting rules for the core theory."""

from __future__ import annotations

from .theory_core import (
    And,
    Constraint,
    Distinct,
    Eq,
    Implies,
    Ite,
    Not,
    Or,
    Value,
    Xor,
)


def rewrite_constraint(term: Constraint) -> Constraint:
    """Simplify the given term."""
    match term:
        case Not(Value(val)):
            """notval"""
            return Value(not val)
        case Not(Not(inner)):
            """notnot: ~(~X) <=> X"""
            return inner
        case Implies(x, y):
            """rwimpl: (X => Y) <=> (Y | ~X)"""
            return Or(y, Not(x))
        case And(Value(True), x) | And(x, Value(True)):
            """andtrue: X & True <=> X"""
            return x
        case And(Value(False), x) | And(x, Value(False)):
            """andfalse: X & False <=> False"""
            return Value(False)
        case And(x, y) if x == y:
            """andself: X & X <=> X"""
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:
            """andunself: X & ~X <=> False"""
            return Value(False)
        case Or(Value(True), x) | Or(x, Value(True)):
            """ortrue: X | True <=> True"""
            return Value(True)
        case Or(Value(False), x) | Or(x, Value(False)):
            """orfalse: X | False <=> X"""
            return x
        case Or(x, y) if x == y:
            """orself: X | X <=> X"""
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:
            """orunself: X | ~X <=> True"""
            return Value(True)
        case Xor(Value(True), x) | Xor(x, Value(True)):
            """xortrue: X ^ True <=> ~X"""
            return Not(x)
        case Xor(Value(False), x) | Xor(x, Value(False)):
            """xorfalse: X ^ False <=> X"""
            return x
        case Xor(x, y) if x == y:
            """xorself: X ^ X <=> False"""
            return Value(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:
            """xorunself: X ^ ~X <=> True"""
            return Value(True)

        # Note: these rules need to be checked for every type of input argument
        # (see the corresponding rules for bitvectors).
        case Eq(Constraint() as x, Constraint() as y):
            """rweq: X = Y <=> ~(X ^ Y)"""
            return Not(Xor(x, y))
        case Distinct(Constraint() as x, Constraint() as y):
            """rwdist: X != Y <=> X ^ Y"""
            return Xor(x, y)
        case Ite(Value(True), x, y):
            """itetrue: True ? X : Y <=> X"""
            return x
        case Ite(Value(False), x, y):
            """itefalse: False ? X : Y <=> Y"""
            return y
        case Ite(_, x, y) if x == y:
            """iteself: C ? X : X <=> X"""
            return x
        case term:
            """fallthrough"""
            return term
