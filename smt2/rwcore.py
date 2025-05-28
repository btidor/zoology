"""Term-rewriting rules for the core theory."""

from .defcore import (
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
        case Not(Value(v)):
            return Value(not v)
        case Not(Not(inner)):  # ~(~X) <=> X
            return inner
        case Implies(x, y):  # (X => Y) <=> (Y | ~X)
            return Or(y, Not(x))
        case And(Value(True), x) | And(x, Value(True)):  # X & True <=> X
            return x
        case And(Value(False), x) | And(x, Value(False)):  # X & False <=> False
            return Value(False)
        case And(x, y) if x == y:  # X & X <=> X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X <=> False
            return Value(False)
        case Or(Value(True), x) | Or(x, Value(True)):  # X | True <=> True
            return Value(True)
        case Or(Value(False), x) | Or(x, Value(False)):  # X | False <=> X
            return x
        case Or(x, y) if x == y:  # X | X <=> X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X <=> True
            return Value(True)
        case Xor(Value(True), x) | Xor(x, Value(True)):  # X ^ True <=> ~X
            return Not(x)
        case Xor(Value(False), x) | Xor(x, Value(False)):  # X ^ False <=> X
            return x
        case Xor(x, y) if x == y:  # X ^ X <=> False
            return Value(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X <=> True
            return Value(True)
        case Eq(Constraint() as x, Constraint() as y):  # X = Y <=> ~(X ^ Y)
            return Not(Xor(x, y))
        case Eq(x, y) if x == y:  # pyright: ignore[reportUnknownVariableType]
            return Value(True)
        case Distinct(Constraint() as x, Constraint() as y):  # X != Y <=> X ^ Y
            return Xor(x, y)
        case Distinct(x, y) if x == y:  # pyright: ignore[reportUnknownVariableType]
            return Value(False)
        case Ite(Value(True), x, y):  # True ? X : Y <=> X
            return x
        case Ite(Value(False), x, y):  # False ? X : Y <=> Y
            return y
        case _:
            return term
