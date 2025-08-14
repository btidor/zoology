"""
Definitions for the theory of bitvectors.

Up-to-date with SMT-LIB version 2.7, QF_BV logic.

See: https://smt-lib.org/logics-all.shtml#QF_BV
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import ClassVar, Iterable, override

from line_profiler import profile

from .bitwuzla import BZLA
from .theory_core import (
    BaseTerm,
    BitwuzlaTerm,
    CTerm,
    CValue,
    DumpContext,
    Eq,
    Kind,
    TermCategory,
)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BTerm(BaseTerm):
    width: int = field(init=False)
    min: int = field(init=False, compare=False)
    max: int = field(init=False, compare=False)

    def sort(self) -> bytes:
        return b"(_ BitVec %d)" % self.width


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BSymbol(BTerm):
    category: ClassVar[TermCategory] = TermCategory.SYMBOL
    name: bytes
    w: InitVar[int]

    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        self.width = w
        super(BSymbol, self).__post_init__()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, self.width)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BValue(BTerm):
    category: ClassVar[TermCategory] = TermCategory.VALUE
    cache: ClassVar[bool] = True
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
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty:
            ctx.write(hex(self.value).encode())
        elif self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.value, self.width)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class UnaryOp(BTerm):
    term: BTerm

    @override
    def __post_init__(self) -> None:
        self.width = self.term.width
        super(UnaryOp, self).__post_init__()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

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
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        super(CompareOp, self).__post_init__()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm

    @override
    def params(self) -> Iterable[int]:
        return (self.i,)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    kind: ClassVar[Kind] = Kind.BV_CONCAT
    terms: tuple[BTerm, ...]

    @override
    def children(self) -> Iterable[BaseTerm]:
        return self.terms

    @override
    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        self.width = reduce(lambda p, q: p + q.width, self.terms, 0)
        super(Concat, self).__post_init__()

    @override
    def dump(self, ctx: DumpContext) -> None:
        terms = self.terms
        if (
            ctx.pretty
            and len(self.terms) > 1
            and isinstance(terms[0], BValue)
            and terms[0].value == 0
        ):
            terms = terms[1:]
        if len(terms) == 1:
            # Bitwuzla doesn't allow single-term Concats.
            terms[0].dump(ctx)
            return
        written = False
        state: tuple[BaseTerm, BTerm, BTerm, int] | None = None
        for term in terms:
            if ctx.pretty and term._pretty == "safe_get":
                res = self.pretty_terms(term)
                if res:
                    if not state:
                        state = (*res, 1)
                        continue
                    elif state[0] == res[0] and Eq(state[2], res[1]) == CValue(True):  # pyright: ignore
                        assert isinstance(state[1], BTerm) and isinstance(state[3], int)
                        state = (state[0], state[1], res[2], state[3] + 1)
                        continue
                if state:
                    if not written:
                        ctx.write(b"(concat")
                        written = True
                    ctx.write(b" ")
                    self.pretty_dump(ctx, *state)
                    state = None
            if not written:
                ctx.write(b"(concat")
                written = True
            ctx.write(b" ")
            term.dump(ctx)
        if state:
            if written:
                ctx.write(b" ")
            self.pretty_dump(ctx, *state)
        if written:
            ctx.write(b")")

    def pretty_terms(self, term: BTerm) -> tuple[BaseTerm, BTerm, BTerm] | None:
        assert isinstance(term, Ite)
        if term.left._pretty == "safe_select":
            st = term.left
        elif term.right._pretty == "safe_select":
            st = term.right
        else:
            return None
        assert isinstance(array := st.array, BaseTerm)  # pyright: ignore
        assert isinstance(key := st.key, BTerm)  # pyright: ignore
        assert isinstance(inc := Add(key, BValue(1, key.width)), BTerm)
        return array, key, inc

    def pretty_dump(
        self, ctx: DumpContext, array: BaseTerm, start: BTerm, end: BTerm, range: int
    ) -> None:
        array.dump(ctx)
        ctx.write(b"[")
        if isinstance(start, BValue) and start.value == 0:
            if isinstance(end, BValue):
                ctx.write(f":{hex(end.value)}]".encode())
            else:
                ctx.write(b":")
                end.dump(ctx)
                ctx.write(b"]")
        else:
            start.dump(ctx)
            if isinstance(end, BValue):
                ctx.write(f":{hex(end.value)}]".encode())
            else:
                ctx.write(f":+{hex(range)}]".encode())


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
    def params(self) -> Iterable[int]:
        return (self.i, self.j)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"
    kind: ClassVar[Kind] = Kind.BV_NOT
    category: ClassVar[TermCategory] = TermCategory.NOT


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    kind: ClassVar[Kind] = Kind.BV_AND
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    kind: ClassVar[Kind] = Kind.BV_OR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"
    kind: ClassVar[Kind] = Kind.BV_NEG


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    kind: ClassVar[Kind] = Kind.BV_ADD
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    kind: ClassVar[Kind] = Kind.BV_MUL
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE


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
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE


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
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)


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
    def children(self) -> Iterable[BaseTerm]:
        return (self.cond, self.left, self.right)

    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty and self._pretty == "safe_get":
            if self.left._pretty == "safe_select":
                self.left.dump(ctx)
                return
            elif self.right._pretty == "safe_select":
                self.right.dump(ctx)
                return
            else:
                self._pretty = None
        super(Ite, self).dump(ctx)
