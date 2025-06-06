"""
Definitions for the theory of bitvectors.

Up-to-date with SMT-LIB version 2.7, QF_BV logic.

See: https://smt-lib.org/logics-all.shtml#QF_BV
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import ClassVar, override

from .theory_core import BaseTerm, CTerm, DumpContext


@dataclass(frozen=True, slots=True)
class BTerm(BaseTerm):
    width: int = field(init=False)

    @abc.abstractmethod
    def __post_init__(self) -> None: ...


@dataclass(frozen=True, slots=True)
class BSymbol(BTerm):
    name: bytes
    w: InitVar[int]

    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (b"(declare-fun %s () (_ BitVec %d))" % (self.name, self.width)),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class BValue(BTerm):
    value: int
    w: InitVar[int]

    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        if self.value < 0:  # convert to two's complement
            object.__setattr__(self, "value", self.value + (1 << w))
        assert 0 <= self.value < (1 << w)
        object.__setattr__(self, "width", w)

    @property
    def sgnd(self) -> int:
        # https://stackoverflow.com/a/9147327 (CC BY-SA 3.0)
        if self.value & (1 << (self.width - 1)):
            return self.value - (1 << self.width)
        return self.value

    @override
    def dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())


@dataclass(frozen=True, slots=True)
class UnaryOp(BTerm):
    term: BTerm

    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, slots=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)


@dataclass(frozen=True, slots=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        assert self.left.width == self.right.width


@dataclass(frozen=True, slots=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm


@dataclass(frozen=True, slots=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    terms: tuple[BTerm, ...]

    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        w = reduce(lambda p, q: p + q.width, self.terms, 0)
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(concat")
        for term in self.terms:
            ctx.write(b" ")
            term.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BTerm

    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        w = self.i - self.j + 1
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"


@dataclass(frozen=True, slots=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(frozen=True, slots=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"


@dataclass(frozen=True, slots=True)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"


@dataclass(frozen=True, slots=True)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"


@dataclass(frozen=True, slots=True)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"


@dataclass(frozen=True, slots=True)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"


@dataclass(frozen=True, slots=True)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"


@dataclass(frozen=True, slots=True)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"


@dataclass(frozen=True, slots=True)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, slots=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(frozen=True, slots=True)
class Comp(BTerm):  # width-1 result
    op: ClassVar[bytes] = b"bvcomp"
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        assert self.left.width == self.right.width


@dataclass(frozen=True, slots=True)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"


@dataclass(frozen=True, slots=True)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"


@dataclass(frozen=True, slots=True)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"


@dataclass(frozen=True, slots=True)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"


@dataclass(frozen=True, slots=True)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"


@dataclass(frozen=True, slots=True)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"

    def __post_init__(self) -> None:
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"

    def __post_init__(self) -> None:
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, slots=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"

    def __post_init__(self) -> None:
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, slots=True)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"


@dataclass(frozen=True, slots=True)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"


@dataclass(frozen=True, slots=True)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"


@dataclass(frozen=True, slots=True)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"


@dataclass(frozen=True, slots=True)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"


@dataclass(frozen=True, slots=True)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"


@dataclass(frozen=True, slots=True)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"


@dataclass(frozen=True, slots=True)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)
