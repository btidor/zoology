"""Definitions and rewrite rules for the core theory."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass, field
from subprocess import PIPE, Popen
from typing import Any, ClassVar, Self, override


@dataclass
class DumpContext:
    out: bytearray = field(default_factory=bytearray)
    defs: dict[bytes, bytes] = field(default_factory=dict[bytes, bytes])

    def add(self, name: bytes, defn: bytes) -> None:
        if name in self.defs:
            assert self.defs[name] == defn
        else:
            self.defs[name] = defn

    def write(self, b: bytes) -> None:
        self.out.extend(b)


def check(*constraints: Constraint) -> bool:
    ctx = DumpContext()
    for constraint in constraints:
        ctx.write(b"(assert ")
        constraint.dump(ctx)
        ctx.write(b")\n")
    ctx.write(b"(check-sat)")

    smt = b"\n".join(ctx.defs.values()) + b"\n" + ctx.out
    print(smt.decode())
    p = Popen(["z3", "-model", "/dev/stdin"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    out, err = p.communicate(smt)
    outs = out.decode().split("\n", 1)
    match outs[0]:
        case "sat":
            return True
        case "unsat":
            return False
        case _:
            raise RuntimeError(out, err, smt)


class Symbolic(abc.ABC):
    __slots__ = ()

    # Instances of Symbolic are expected to be immutable:
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    @abc.abstractmethod
    def dump(self, ctx: DumpContext) -> None: ...

    @abc.abstractmethod
    def reveal(self) -> Any: ...


class Constraint(Symbolic):
    __slots__ = ()

    def reveal(self) -> bool | None:
        return None


@dataclass(frozen=True, slots=True)
class Symbol(Constraint):
    name: bytes

    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class Value(Constraint):
    value: bool

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @override
    def reveal(self) -> bool | None:
        return self.value


@dataclass(frozen=True, slots=True)
class Not(Constraint):
    term: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(not ")
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class BinaryOp(Constraint):
    op: ClassVar[bytes]
    left: Constraint
    right: Constraint

    def dump(self, ctx: DumpContext) -> None:
        assert self.op
        ctx.write(b"(%b " % self.op)
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


class Implies(BinaryOp):
    __slots__ = ()
    op: ClassVar[bytes] = b"=>"


class And(BinaryOp):
    __slots__ = ()
    op: ClassVar[bytes] = b"and"


class Or(BinaryOp):
    __slots__ = ()
    op: ClassVar[bytes] = b"or"


class Xor(BinaryOp):
    __slots__ = ()
    op: ClassVar[bytes] = b"xor"


@dataclass(frozen=True, slots=True)
class Eq[S: Symbolic](Constraint):
    left: S
    right: S

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(= ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Distinct[S: Symbolic](Constraint):
    left: S
    right: S

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(distinct ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Ite(Constraint):
    cond: Constraint
    left: Constraint
    right: Constraint

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(ite ")
        self.cond.dump(ctx)
        ctx.write(b" ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


def rewrite(term: Constraint) -> Constraint:
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
