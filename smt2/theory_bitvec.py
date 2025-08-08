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

from .theory_core import BZLA, CACHE, BaseTerm, BitwuzlaTerm, CTerm, DumpContext, Kind


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

    @override
    def bzla(self) -> BitwuzlaTerm:
        global CACHE
        if self.name not in CACHE:
            CACHE[self.name] = BZLA.mk_const(
                BZLA.mk_bv_sort(self.width), self.name.decode()
            )
        return CACHE[self.name]


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

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_bv_value(BZLA.mk_bv_sort(self.width), self.value)
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class UnaryOp(BTerm):
    term: BTerm

    @override
    def __post_init__(self) -> None:
        self.width = self.term.width
        super(UnaryOp, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.term.bzla(),))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(BinaryOp, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        super(CompareOp, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.term.bzla(),), (self.i,))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    kind: ClassVar[Kind] = Kind.BV_CONCAT
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

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, tuple(t.bzla() for t in self.terms))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    kind: ClassVar[Kind] = Kind.BV_EXTRACT
    i: int
    j: int
    term: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        self.width = self.i - self.j + 1
        super(Extract, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.term.bzla(),), (self.i, self.j))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"
    kind: ClassVar[Kind] = Kind.BV_NOT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    kind: ClassVar[Kind] = Kind.BV_AND
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    kind: ClassVar[Kind] = Kind.BV_OR
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"
    kind: ClassVar[Kind] = Kind.BV_NEG


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    kind: ClassVar[Kind] = Kind.BV_ADD
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    kind: ClassVar[Kind] = Kind.BV_MUL
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"
    kind: ClassVar[Kind] = Kind.BV_UDIV


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"
    kind: ClassVar[Kind] = Kind.BV_UREM


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"
    kind: ClassVar[Kind] = Kind.BV_SHL


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"
    kind: ClassVar[Kind] = Kind.BV_SHR


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"
    kind: ClassVar[Kind] = Kind.BV_ULT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"
    kind: ClassVar[Kind] = Kind.BV_NAND


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"
    kind: ClassVar[Kind] = Kind.BV_NOR


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    kind: ClassVar[Kind] = Kind.BV_XOR
    commutative: ClassVar[bool] = True


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"
    kind: ClassVar[Kind] = Kind.BV_XNOR


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Comp(BTerm):  # width-1 result
    op: ClassVar[bytes] = b"bvcomp"
    kind: ClassVar[Kind] = Kind.BV_COMP
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = 1
        super(Comp, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"
    kind: ClassVar[Kind] = Kind.BV_SUB


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"
    kind: ClassVar[Kind] = Kind.BV_SDIV


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"
    kind: ClassVar[Kind] = Kind.BV_SREM


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"
    kind: ClassVar[Kind] = Kind.BV_SMOD


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"
    kind: ClassVar[Kind] = Kind.BV_ASHR


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"
    kind: ClassVar[Kind] = Kind.BV_REPEAT

    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        self.width = self.term.width * self.i
        super(Repeat, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"
    kind: ClassVar[Kind] = Kind.BV_ZERO_EXTEND

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(ZeroExtend, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"
    kind: ClassVar[Kind] = Kind.BV_SIGN_EXTEND

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(SignExtend, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"
    kind: ClassVar[Kind] = Kind.BV_ROL

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateLeft, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"
    kind: ClassVar[Kind] = Kind.BV_ROR

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateRight, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"
    kind: ClassVar[Kind] = Kind.BV_ULE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"
    kind: ClassVar[Kind] = Kind.BV_UGT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"
    kind: ClassVar[Kind] = Kind.BV_UGE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"
    kind: ClassVar[Kind] = Kind.BV_SLT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"
    kind: ClassVar[Kind] = Kind.BV_SLE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"
    kind: ClassVar[Kind] = Kind.BV_SGT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"
    kind: ClassVar[Kind] = Kind.BV_SGE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: BTerm
    right: BTerm

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(Ite, self).__post_init__()

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(
                self.kind, (self.cond.bzla(), self.left.bzla(), self.right.bzla())
            )
        return self._bzla
