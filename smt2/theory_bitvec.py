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

from line_profiler import profile

from .theory_core import BaseTerm, CTerm, DumpContext


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BTerm(BaseTerm):
    width: int = field(init=False)
    min: int = field(init=False, compare=False)
    max: int = field(init=False, compare=False)

    def sort(self) -> bytes:
        return b"(_ BitVec %d)" % self.width


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BSymbol(BTerm):
    name: bytes
    w: InitVar[int]

    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        self.width = w
        super(BSymbol, self).__post_init__()

    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BValue(BTerm):
    value: int
    w: InitVar[int]

    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        if self.value < 0:  # convert to two's complement
            self.value = self.value + (1 << w)
        assert 0 <= self.value < (1 << w)
        self.width = w
        super(BValue, self).__post_init__()

    @property
    @profile
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


@dataclass(repr=False, slots=True, unsafe_hash=True)
class UnaryOp(BTerm):
    term: BTerm

    @override
    def __post_init__(self) -> None:
        self.width = self.term.width
        super(UnaryOp, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(BinaryOp, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        super(CompareOp, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    terms: tuple[BTerm, ...]

    @override
    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        self.width = reduce(lambda p, q: p + q.width, self.terms, 0)
        super(Concat, self).__post_init__()
        self.count = reduce(int.__add__, (t.count + 1 for t in self.terms))

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


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        self.width = self.i - self.j + 1
        super(Extract, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Comp(BTerm):  # width-1 result
    op: ClassVar[bytes] = b"bvcomp"
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = 1
        super(Comp, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"

    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        self.width = self.term.width * self.i
        super(Repeat, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(ZeroExtend, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(SignExtend, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateLeft, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateRight, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(Ite, self).__post_init__()
