"""Definitions and rewrite rules for the theory of bitvectors."""
# ruff: noqa

from __future__ import annotations

from dataclasses import dataclass
from typing import override

from ._core import Constraint, DumpContext, Symbolic


class BitVector[N: int](Symbolic):
    __slots__ = ()

    def reveal(self) -> int | None:
        return None


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
class Extract[N: int](BitVector[N]):
    i: int
    j: int
    term: BitVector[int]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"((_ extract %d %d) " % (self.i, self.j))
        self.term.dump(ctx)
        ctx.write(b")")


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
class Neg[N: int](BitVector[N]):
    term: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvneg ")
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Add[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvadd ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Mul[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvmul ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Udiv[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvudiv ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Urem[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvurem ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Shl[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvshl ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Lshr[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvlshr ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Ult[N: int](Constraint):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvult ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Xor[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvxor ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Sub[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvsub ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Sdiv[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvsdiv ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Srem[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvsrem ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Smod[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvsmod ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class ZeroExtend[N: int](BitVector[N]):
    i: int
    term: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"((_ zero_extend %d) " % self.i)
        self.term.dump(ctx)
        ctx.write(b")")


def rewrite[N: int](term: BitVector[N], width: N) -> BitVector[N]:
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Not(Value(v)):
            return Value(mask ^ v, width)
        case Not(Not(inner)):  # ~(~X) => X
            return inner
        case And(Value(p), Value(q)):
            return Value(p & q, width)
        case And(Value(m), x) | And(x, Value(m)) if m == mask:  # X & 1111 => X
            return x
        case And(Value(0), x) | And(x, Value(0)):  # X & 0000 => 0000
            return Value(0, width)
        case And(x, y) if x == y:  # X & X => X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X => 0000
            return Value(0, width)
        case Or(Value(p), Value(q)):
            return Value(p | q, width)
        case Or(Value(m), x) | Or(x, Value(m)) if m == mask:  # X | 1111 => 1111
            return Value(mask, width)
        case Or(Value(0), x) | Or(x, Value(0)):  # X | 0000 => X
            return x
        case Or(x, y) if x == y:  # X | X => X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X => 1111
            return Value(mask, width)
        case Xor(Value(p), Value(q)):
            return Value(p ^ q, width)
        case Xor(Value(m), x) | Xor(x, Value(m)) if m == modulus:  # X ^ 1111 => ~X
            return Not(x)
        case Xor(Value(0), x) | Xor(x, Value(0)):  # X ^ 0000 => X
            return x
        case Xor(x, y) if x == y:  # X ^ X => 0000
            return Value(0, width)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X => 1111
            return Value(mask, width)
        case Add(Value(p), Value(q)):
            return Value((p + q) % modulus, width)
        case _:
            return term
