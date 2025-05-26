"""Definitions and rewrite rules for the theory of bitvectors."""
# ruff: noqa

from __future__ import annotations
import abc
from dataclasses import dataclass
from typing import Any, Self, override

from ._base import DumpContext


class BitVector[N: int](abc.ABC):
    __slots__ = ()

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    @abc.abstractmethod
    def dump(self, ctx: DumpContext) -> None: ...

    def reveal(self) -> int | None:
        return None


@dataclass(frozen=True, slots=True)
class Value[N: int](BitVector[N]):
    value: int
    width: N

    def __post_init__(self):
        assert 0 <= self.value < (1 << self.width)

    def dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())

    @override
    def reveal(self) -> int | None:
        return self.value


@dataclass(frozen=True, slots=True)
class Symbol[N: int](BitVector[N]):
    name: bytes
    width: N

    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (b"(declare-fun %s () (_ BitVec %d))" % (self.name, self.width)),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class Not[N: int](BitVector[N]):
    term: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvnot ")
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class And[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvand ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Or[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvor ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Xor[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(xor ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


def rewrite[N: int](term: BitVector[N], width: N) -> BitVector[N]:
    mask = (1 << width) - 1
    match term:
        case Not(Value(v, width)):
            return Value(mask ^ v, width)
        case Not(Not(inner)):  # ~(~X) => X
            return inner
        case And(Value(mask), x) | And(x, Value(mask)):  # X & 1111 => X
            return x
        case And(Value(0), x) | And(x, Value(0)):  # X & 0000 => 0000
            return Value(0, width)
        case And(x, y) if x == y:  # X & X => X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X => 0000
            return Value(0, width)
        case Or(Value(mask), x) | Or(x, Value(mask)):  # X | 1111 => 1111
            return Value(mask, width)
        case Or(Value(0), x) | Or(x, Value(0)):  # X | 0000 => X
            return x
        case Or(x, y) if x == y:  # X | X => X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X => 1111
            return Value(mask, width)
        case Xor(Value(mask), x) | Xor(x, Value(mask)):  # X ^ 1111 => ~X
            return Not(x)
        case Xor(Value(0), x) | Xor(x, Value(0)):  # X ^ 0000 => X
            return x
        case Xor(x, y) if x == y:  # X ^ X => 0000
            return Value(0, width)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X => 1111
            return Value(mask, width)
        case _:
            return term
