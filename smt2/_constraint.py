"""Definitions and rewrite rules for boolean constraints."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass
from typing import Any, Self, override

from ._base import DumpContext


class Constraint(abc.ABC):
    __slots__ = ()

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    @abc.abstractmethod
    def dump(self, ctx: DumpContext) -> None: ...

    def reveal(self) -> bool | None:
        return None


@dataclass(frozen=True, slots=True)
class Value(Constraint):
    value: bool

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @override
    def reveal(self) -> bool | None:
        return self.value


@dataclass(frozen=True, slots=True)
class Symbol(Constraint):
    name: bytes

    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class Not(Constraint):
    term: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(not ")
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class And(Constraint):
    left: Constraint
    right: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(and ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Or(Constraint):
    left: Constraint
    right: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(or ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Xor(Constraint):
    left: Constraint
    right: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(xor ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


def rewrite(term: Constraint) -> Constraint:
    match term:
        case Not(Value(v)):
            return Value(not v)
        case Not(Not(inner)):  # ~(~X) => X
            return inner
        case And(Value(True), x) | And(x, Value(True)):  # X & True => X
            return x
        case And(Value(False), x) | And(x, Value(False)):  # X & False => False
            return Value(False)
        case And(x, y) if x == y:  # X & X => X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X => False
            return Value(False)
        case Or(Value(True), x) | Or(x, Value(True)):  # X | True => True
            return Value(True)
        case Or(Value(False), x) | Or(x, Value(False)):  # X | False => X
            return x
        case Or(x, y) if x == y:  # X | X => X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X => True
            return Value(True)
        case Xor(Value(True), x) | Xor(x, Value(True)):  # X ^ True => ~X
            return Not(x)
        case Xor(Value(False), x) | Xor(x, Value(False)):  # X ^ False => X
            return x
        case Xor(x, y) if x == y:  # X ^ X => False
            return Value(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X => True
            return Value(True)
        case _:
            return term
