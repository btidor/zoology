"""
Definitions for the theory of bitvectors.

Up-to-date with SMT-LIB version 2.7, QF_BV logic.

See: https://smt-lib.org/logics-all.shtml#QF_BV
"""
# ruff: noqa

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar, Literal, override

from .defcore import Constraint, DumpContext, Symbolic


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
class UnaryOp[N: int](BitVector[N]):
    op: ClassVar[bytes]
    term: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(%b " % self.op)
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class BinaryOp[N: int](BitVector[N]):
    op: ClassVar[bytes]
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        assert self.op
        ctx.write(b"(%b " % self.op)
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class CompareOp[N: int](Constraint):
    op: ClassVar[bytes]
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(%b " % self.op)
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class SingleParamOp[N: int](BitVector[N]):
    op: ClassVar[bytes]
    i: int
    term: BitVector[int]

    def __post_init__(self):
        assert self.i >= 0

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"((_ %b %d) " % (self.op, self.i))
        self.term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Concat[N: int](BitVector[N]):
    terms: tuple[BitVector[int]]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(concat")
        for term in self.terms:
            ctx.write(b" ")
            term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Extract[N: int](BitVector[N]):
    i: int
    j: int
    term: BitVector[int]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"((_ extract %d %d) " % (self.i, self.j))
        self.term.dump(ctx)
        ctx.write(b")")


class Not[N: int](UnaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvnot"


class And[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvand"


class Or[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvor"


class Neg[N: int](UnaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvneg"


class Add[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvadd"


class Mul[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvmul"


class Udiv[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvudiv"


class Urem[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvurem"


class Shl[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvshl"


class Lshr[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvlshr"


class Ult[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvult"


class Nand[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvnand"


class Nor[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvnor"


class Xor[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvxor"


class Xnor[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvxnor"


class Comp[N: int](BitVector[Literal[1]]):
    left: BitVector[N]
    right: BitVector[N]

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvcomp ")
        self.left.dump(ctx)
        ctx.write(b" ")
        self.right.dump(ctx)
        ctx.write(b")")


class Sub[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsub"


class Sdiv[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsdiv"


class Srem[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsrem"


class Smod[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsmod"


class Ashr[N: int](BinaryOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvashr"


class Repeat[N: int](SingleParamOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"repeat"

    def __post_init__(self):
        assert self.i >= 1


class ZeroExtend[N: int](SingleParamOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"zero_extend"


class SignExtend[N: int](SingleParamOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"sign_extend"


class RotateLeft[N: int](SingleParamOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"rotate_left"


class RotateRight[N: int](SingleParamOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"rotate_right"


class Ule[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvule"


class Ugt[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvugt"


class Uge[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvuge"


class Slt[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvslt"


class Sle[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsle"


class Sgt[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsgt"


class Sge[N: int](CompareOp[N]):
    __slots__ = ()
    op: ClassVar[bytes] = b"bvsge"
