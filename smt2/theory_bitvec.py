"""
Definitions for the theory of bitvectors.

Up-to-date with SMT-LIB version 2.7, QF_BV logic.

See: https://smt-lib.org/logics-all.shtml#QF_BV
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import ClassVar, override

from .theory_core import BaseTerm, CTerm, DumpContext


@dataclass(frozen=True, repr=False, slots=True)
class BTerm(BaseTerm):
    width: int = field(init=False)
    min: int = field(init=False, compare=False)
    max: int = field(init=False, compare=False)

    def sort(self) -> bytes:
        return b"(_ BitVec %d)" % self.width


@dataclass(frozen=True, repr=False, slots=True)
class BSymbol(BTerm):
    name: bytes
    w: InitVar[int]

    def __post_init__(self, w: int) -> None:
        BaseTerm.__post_init__(self)
        assert w > 0, "width must be positive"
        object.__setattr__(self, "width", w)

    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


@dataclass(frozen=True, repr=False, slots=True)
class BValue(BTerm):
    value: int
    w: InitVar[int]

    def __post_init__(self, w: int) -> None:
        BaseTerm.__post_init__(self)
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

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, repr=False, slots=True)
class UnaryOp(BTerm):
    term: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, repr=False, slots=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)


@dataclass(frozen=True, repr=False, slots=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.left.width == self.right.width


@dataclass(frozen=True, repr=False, slots=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm


@dataclass(frozen=True, repr=False, slots=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    terms: tuple[BTerm, ...]

    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        descendants = reduce(int.__add__, (t.descendants + 1 for t in self.terms))
        object.__setattr__(self, "descendants", descendants)
        w = reduce(lambda p, q: p + q.width, self.terms, 0)
        object.__setattr__(self, "width", w)

    @override
    def walk(self, ctx: DumpContext) -> None:
        if ctx.visit(self):
            return
        for term in self.terms:
            term.walk(ctx)

    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.try_alias(self):
            return
        if len(self.terms) == 1:
            # Bitwuzla doesn't allow single-term Concats.
            self.terms[0].dump(ctx)
        else:
            ctx.write(b"(concat")
            for term in self.terms:
                ctx.write(b" ")
                term.dump(ctx)
            ctx.write(b")")


@dataclass(frozen=True, repr=False, slots=True)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.term.width > self.i >= self.j >= 0
        w = self.i - self.j + 1
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, repr=False, slots=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"


@dataclass(frozen=True, repr=False, slots=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, repr=False, slots=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, repr=False, slots=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(frozen=True, repr=False, slots=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, repr=False, slots=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, repr=False, slots=True)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"


@dataclass(frozen=True, repr=False, slots=True)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"


@dataclass(frozen=True, repr=False, slots=True)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"


@dataclass(frozen=True, repr=False, slots=True)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"


@dataclass(frozen=True, repr=False, slots=True)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"


@dataclass(frozen=True, repr=False, slots=True)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"


@dataclass(frozen=True, repr=False, slots=True)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"


@dataclass(frozen=True, repr=False, slots=True)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    commutative: ClassVar[bool] = True


@dataclass(frozen=True, repr=False, slots=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(frozen=True, repr=False, slots=True)
class Comp(BTerm):  # width-1 result
    op: ClassVar[bytes] = b"bvcomp"
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", 1)


@dataclass(frozen=True, repr=False, slots=True)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"


@dataclass(frozen=True, repr=False, slots=True)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"


@dataclass(frozen=True, repr=False, slots=True)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"


@dataclass(frozen=True, repr=False, slots=True)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"


@dataclass(frozen=True, repr=False, slots=True)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"


@dataclass(frozen=True, repr=False, slots=True)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, repr=False, slots=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, repr=False, slots=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, repr=False, slots=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, repr=False, slots=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, repr=False, slots=True)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"


@dataclass(frozen=True, repr=False, slots=True)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"


@dataclass(frozen=True, repr=False, slots=True)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"


@dataclass(frozen=True, repr=False, slots=True)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"


@dataclass(frozen=True, repr=False, slots=True)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"


@dataclass(frozen=True, repr=False, slots=True)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"


@dataclass(frozen=True, repr=False, slots=True)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"


@dataclass(frozen=True, repr=False, slots=True)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)
