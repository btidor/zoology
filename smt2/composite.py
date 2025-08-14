"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analyze_composite

"""
# ruff: noqa: D101, D102, D103
# pyright: reportAttributeAccessIssue=false
# pyright: reportUnknownMemberType=false
# pyright: reportUnknownVariableType=false

from __future__ import annotations

import abc
import copy
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, Iterable, Self, override

from line_profiler import profile

from .bitwuzla import BZLA
from .theory_core import BaseTerm, BitwuzlaTerm, DumpContext, Kind, TermCategory

type MinMax = tuple[int, int]


@dataclass(repr=False, slots=True, eq=False)
class CTerm(BaseTerm):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(repr=False, slots=True, eq=False)
class CSymbol(CTerm):
    category: ClassVar[TermCategory] = TermCategory.SYMBOL
    name: bytes

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, None)


@dataclass(repr=False, slots=True, eq=False)
class CValue(CTerm):
    category: ClassVar[TermCategory] = TermCategory.VALUE
    value: bool

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.value, None)


@dataclass(repr=False, slots=True, eq=False)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    kind: ClassVar[Kind] = Kind.NOT
    category: ClassVar[TermCategory] = TermCategory.NOT
    term: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Not(CValue(a)):
                return CValue(not a)
            case Not(Not(inner)):
                return inner
            case Not(And(x, y)):
                return Or(Not(x), Not(y))
            case Not(Or(x, y)):
                return And(Not(x), Not(y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    kind: ClassVar[Kind] = Kind.IMPLIES
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Implies(x, y):
                return Or(y, Not(x))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    kind: ClassVar[Kind] = Kind.AND
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case And(CValue(a), CValue(b)):
                return CValue(a and b)
            case And(CValue(True), x):
                return x
            case And(CValue(False), x):
                return CValue(False)
            case And(x, y) if x == y:
                return x
            case And(x, Not(y)) if x == y:
                return CValue(False)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    kind: ClassVar[Kind] = Kind.OR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Or(CValue(a), CValue(b)):
                return CValue(a or b)
            case Or(CValue(True), x):
                return CValue(True)
            case Or(CValue(False), x):
                return x
            case Or(x, y) if x == y:
                return x
            case Or(x, Not(y)) if x == y:
                return CValue(True)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    kind: ClassVar[Kind] = Kind.XOR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Xor(CValue(a), CValue(b)):
                return CValue(a != b)
            case Xor(CValue(True), x):
                return Not(x)
            case Xor(CValue(False), x):
                return x
            case Xor(x, y) if x == y:
                return CValue(False)
            case Xor(x, Not(y)) if x == y:
                return CValue(True)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    kind: ClassVar[Kind] = Kind.EQUAL
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: S
    right: S

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def __post_init__(self) -> None:
        super(Eq, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Eq(CTerm() as x, CTerm() as y):
                return Not(Xor(x, y))
            case Eq(BValue(a), BValue(b)):
                return CValue(a == b)
            case Eq(BTerm() as x, BTerm() as y) if x == y:
                return CValue(True)
            case Eq(BTerm() as x, BNot(y)) if x == y:
                return CValue(False)
            case Eq(BValue(a), BNot(x)):
                mask = (1 << x.width) - 1
                return Eq(BValue(mask ^ a, x.width), x)
            case Eq(BValue(a), BAnd(BValue(b), x)) if a & (b ^ (1 << x.width) - 1) != 0:
                return CValue(False)
            case Eq(BValue(a), BOr(BValue(b), x)) if (a ^ (1 << x.width) - 1) & b != 0:
                return CValue(False)
            case Eq(BValue(a), BXor(BValue(b), x)):
                return Eq(BValue(a ^ b, x.width), x)
            case Eq(BValue(a), Add(x, BNot(y))) if a == (1 << x.width) - 1:
                return Eq(x, y)
            case Eq(BValue(a), Add(BValue(b), x)):
                return Eq(BValue((a - b) % (1 << x.width), x.width), x)
            case Eq(Add(BValue(a), x), Add(BValue(b), y)) if x == y:
                return CValue(a == b)
            case Eq(BTerm() as z, Ite(c, x, y)) if z == x:
                return Or(c, Eq(z, y))
            case Eq(BTerm() as z, Ite(c, x, y)) if z == y:
                return Or(Not(c), Eq(z, x))
            case Eq(BValue(a) as v, Ite(c, BValue(p), y)) if a != p:
                return And(Not(c), Eq(v, y))
            case Eq(BValue(a) as v, Ite(c, x, BValue(q))) if a != q:
                return And(c, Eq(v, x))
            case Eq(BValue(a) as x, Concat([BValue(b) as y, *rest])) if len(rest) > 0:
                rwidth = x.width - y.width
                return And(
                    CValue(a >> rwidth == b),
                    Eq(BValue(a & (1 << rwidth) - 1, rwidth), Concat((*rest,))),
                )
            case Eq(BTerm() as x, BTerm() as y) if x.max < y.min:
                return CValue(False)
            case Eq(BTerm() as x, BTerm() as y) if y.max < x.min:
                return CValue(False)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    kind: ClassVar[Kind] = Kind.DISTINCT
    left: S
    right: S

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def __post_init__(self) -> None:
        super(Distinct, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Distinct(CTerm() as x, CTerm() as y):
                return Xor(x, y)
            case Distinct(BTerm() as x, BTerm() as y):
                return Not(Eq(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.cond, self.left, self.right)

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case CIte(c, x, y):
                return Or(And(c, x), And(Not(c), y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class BTerm(BaseTerm):
    width: int = field(init=False)
    min: int = field(init=False, compare=False)
    max: int = field(init=False, compare=False)

    def sort(self) -> bytes:
        return b"(_ BitVec %d)" % self.width


@dataclass(repr=False, slots=True, eq=False)
class BSymbol(BTerm):
    category: ClassVar[TermCategory] = TermCategory.SYMBOL
    name: bytes
    w: InitVar[int]

    @profile
    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        self.width = w
        super(BSymbol, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, self.width)


@dataclass(repr=False, slots=True, eq=False)
class BValue(BTerm):
    category: ClassVar[TermCategory] = TermCategory.VALUE
    cache: ClassVar[bool] = True
    value: int
    w: InitVar[int]

    @profile
    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        if self.value < 0:
            self.value = self.value + (1 << w)
        assert 0 <= self.value < 1 << w
        self.width = w
        super(BValue, self).__post_init__()
        self.min = self.value
        self.max = self.value

    @property
    @profile
    def sgnd(self) -> int:
        if self.value & 1 << self.width - 1:
            return self.value - (1 << self.width)
        return self.value

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty:
            ctx.write(hex(self.value).encode())
        elif self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.value, self.width)


@dataclass(repr=False, slots=True, eq=False)
class UnaryOp(BTerm):
    term: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        self.width = self.term.width
        super(UnaryOp, self).__post_init__()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, eq=False)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(BinaryOp, self).__post_init__()


@dataclass(repr=False, slots=True, eq=False)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        super(CompareOp, self).__post_init__()


@dataclass(repr=False, slots=True, eq=False)
class SingleParamOp(BTerm):
    i: int
    term: BTerm

    @override
    def params(self) -> Iterable[int]:
        return (self.i,)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, eq=False)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    kind: ClassVar[Kind] = Kind.BV_CONCAT
    terms: tuple[BTerm, ...]

    @override
    def children(self) -> Iterable[BaseTerm]:
        return self.terms

    @profile
    @override
    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        self.width = reduce(lambda p, q: p + q.width, self.terms, 0)
        super(Concat, self).__post_init__()
        if len(self.terms) == 2 and isinstance(self.terms[0], BValue):
            self.min = self.terms[1].min | self.terms[0].value << self.terms[1].width
            self.max = self.terms[1].max | self.terms[0].value << self.terms[1].width
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        terms = self.terms
        if (
            ctx.pretty
            and len(self.terms) > 1
            and isinstance(terms[0], BValue)
            and (terms[0].value == 0)
        ):
            terms = terms[1:]
        if len(terms) == 1:
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
                    elif state[0] == res[0] and Eq(state[2], res[1]) == CValue(True):
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
        assert isinstance((array := st.array), BaseTerm)
        assert isinstance((key := st.key), BTerm)
        assert isinstance((inc := Add(key, BValue(1, key.width))), BTerm)
        return (array, key, inc)

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

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Concat([single]):
                return single
            case Concat([BValue(a) as x, BValue(b) as y, *rest]):
                return Concat((BValue(a << y.width | b, x.width + y.width), *rest))
            case Concat([*rest, BValue(a) as x, BValue(b) as y]):
                return Concat((*rest, BValue(a << y.width | b, x.width + y.width)))
            case Concat([*left, Concat([*right])]):
                return Concat((*left, *right))
            case Concat([Concat([*left]), *right]):
                return Concat((*left, *right))
            case Concat([Extract(i, j, x), Extract(k, l, y), *rest]) if (
                j == k + 1 and x == y
            ):
                return Concat((Extract(i, l, x), *rest))
            case Concat([*rest, Extract(i, j, x), Extract(k, l, y)]) if (
                j == k + 1 and x == y
            ):
                return Concat((*rest, Extract(i, l, x)))
            case Concat([*rest, Extract(i, j, x), Extract(k, l, y), z]) if (
                j == k + 1 and x == y
            ):
                return Concat((*rest, Extract(i, l, x), z))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    kind: ClassVar[Kind] = Kind.BV_EXTRACT
    i: int
    j: int
    term: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        self.width = self.i - self.j + 1
        super(Extract, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @override
    def params(self) -> Iterable[int]:
        return (self.i, self.j)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Extract(i, j, BValue(a)):
                return BValue(a >> j & (1 << i - j + 1) - 1, i - j + 1)
            case Extract(i, j, x) if i == x.width - 1 and j == 0:
                return x
            case Extract(i, j, Concat([*rest, x])) if i < x.width:
                return Extract(i, j, x)
            case Extract(i, j, Concat([*rest, x])) if j >= x.width:
                return Extract(i - x.width, j - x.width, Concat((*rest,)))
            case Extract(i, j, Concat([x, *rest]) as c) if j >= c.width - x.width:
                return Extract(i - c.width + x.width, j - c.width + x.width, x)
            case Extract(i, j, Concat([x, *rest]) as c) if i < c.width - x.width:
                return Extract(i, j, Concat((*rest,)))
            case Extract(i, j, Ite(c, BValue() as x, BValue() as y)):
                return Ite(c, Extract(i, j, x), Extract(i, j, y))
            case Extract(i, j, BAnd(BValue(a), x)):
                return BAnd(
                    BValue(a >> j & (1 << i - j + 1) - 1, i - j + 1), Extract(i, j, x)
                )
            case Extract(i, j, BOr(BValue(a), x)):
                return BOr(
                    BValue(a >> j & (1 << i - j + 1) - 1, i - j + 1), Extract(i, j, x)
                )
            case Extract(i, j, BXor(BValue(a), x)):
                return BXor(
                    BValue(a >> j & (1 << i - j + 1) - 1, i - j + 1), Extract(i, j, x)
                )
            case Extract(i, j, Lshr(x, BValue(shift))) if i < x.width - shift:
                return Extract(i + shift, j + shift, x)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"
    kind: ClassVar[Kind] = Kind.BV_NOT
    category: ClassVar[TermCategory] = TermCategory.NOT

    @profile
    def __post_init__(self) -> None:
        super(BNot, self).__post_init__()
        self.min = self.term.max ^ (1 << self.width) - 1
        self.max = self.term.min ^ (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case BNot(BValue(a)):
                return BValue(a ^ mask, width)
            case BNot(BNot(inner)):
                return inner
            case BNot(Add(x, y)):
                return Add(BValue(1, width), Add(BNot(x), BNot(y)))
            case BNot(Ite(c, x, y)):
                return Ite(c, BNot(x), BNot(y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    kind: ClassVar[Kind] = Kind.BV_AND
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE

    @profile
    def __post_init__(self) -> None:
        super(BAnd, self).__post_init__()
        self.min = 0
        self.max = min(self.left.max, self.right.max)

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case BAnd(BValue(a), BValue(b)):
                return BValue(a & b, width)
            case BAnd(BValue(0), x):
                return BValue(0, width)
            case BAnd(BValue(m), x) if m == mask:
                return x
            case BAnd(x, y) if x == y:
                return x
            case BAnd(x, BNot(y)) if x == y:
                return BValue(0, width)
            case BAnd(BValue(a), BAnd(BValue(b), x)):
                return BAnd(BValue(a & b, width), x)
            case BAnd(Ite(c, x, y), z):
                return Ite(c, BAnd(x, z), BAnd(y, z))
            case BAnd(z, Ite(c, x, y)):
                return Ite(c, BAnd(x, z), BAnd(y, z))
            case BAnd(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
                mask = (1 << x.width) - 1
                return Concat(
                    (
                        BAnd(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                        BAnd(BValue(a & mask, x.width), x),
                    )
                )
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    kind: ClassVar[Kind] = Kind.BV_OR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE

    @profile
    def __post_init__(self) -> None:
        super(BOr, self).__post_init__()
        self.min = max(self.left.min, self.right.min)
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case BOr(BValue(a), BValue(b)):
                return BValue(a | b, width)
            case BOr(BValue(0), x):
                return x
            case BOr(BValue(m), x) if m == mask:
                return BValue(mask, width)
            case BOr(x, y) if x == y:
                return x
            case BOr(x, BNot(y)) if x == y:
                return BValue(mask, width)
            case BOr(BValue(a), BOr(BValue(b), x)):
                return BOr(BValue(a | b, width), x)
            case BOr(Ite(c, x, y), z):
                return Ite(c, BOr(x, z), BOr(y, z))
            case BOr(z, Ite(c, x, y)):
                return Ite(c, BOr(x, z), BOr(y, z))
            case BOr(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
                mask = (1 << x.width) - 1
                return Concat(
                    (
                        BOr(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                        BOr(BValue(a & mask, x.width), x),
                    )
                )
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"
    kind: ClassVar[Kind] = Kind.BV_NEG

    @profile
    def __post_init__(self) -> None:
        super(Neg, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Neg(x):
                return Add(BValue(1, self.width), BNot(x))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    kind: ClassVar[Kind] = Kind.BV_ADD
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE

    @profile
    def __post_init__(self) -> None:
        super(Add, self).__post_init__()
        if self.left.max < 1 << self.width - 1 and self.right.max < 1 << self.width - 1:
            self.min = self.left.min + self.right.min
            self.max = self.left.max + self.right.max
        elif (
            isinstance(self.left, BValue)
            and self.left.sgnd < 0
            and (self.right.min + self.left.sgnd > 0)
        ):
            self.min = self.right.min + self.left.sgnd
            self.max = self.right.max + self.left.sgnd
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        modulus = 1 << width
        match self:
            case Add(BValue(a), BValue(b)):
                return BValue((a + b) % modulus, width)
            case Add(BValue(0), x):
                return x
            case Add(x, BNot(y)) if x == y:
                return BValue(mask, width)
            case Add(x, Add(y, BNot(z))) if x == z:
                return Add(BValue(mask, width), y)
            case Add(BValue(a), Add(BValue(b), x)):
                return Add(BValue((a + b) % modulus, width), x)
            case Add(Add(BValue(a), x), Add(BValue(b), y)):
                return Add(BValue((a + b) % modulus, width), Add(x, y))
            case Add(Add(BValue(a) as z, x), y):
                return Add(z, Add(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    kind: ClassVar[Kind] = Kind.BV_MUL
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE

    @profile
    def __post_init__(self) -> None:
        super(Mul, self).__post_init__()
        if (
            isinstance(self.left, BValue)
            and self.left.value * self.right.max <= (1 << self.width) - 1
        ):
            self.min = self.left.value * self.right.min
            self.max = self.left.value * self.right.max
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        modulus = 1 << width
        match self:
            case Mul(BValue(a), BValue(b)):
                return BValue(a * b % modulus, width)
            case Mul(BValue(0), x):
                return BValue(0, width)
            case Mul(BValue(1), x):
                return x
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"
    kind: ClassVar[Kind] = Kind.BV_UDIV

    @profile
    def __post_init__(self) -> None:
        super(Udiv, self).__post_init__()
        if isinstance(self.right, BValue) and self.right.value != 0:
            self.min = self.left.min // self.right.value
            self.max = self.left.max // self.right.value
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case Udiv(BValue(a), BValue(b)) if b != 0:
                return BValue(a // b, width)
            case Udiv(x, BValue(0)):
                return BValue(mask, width)
            case Udiv(x, BValue(1)):
                return x
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"
    kind: ClassVar[Kind] = Kind.BV_UREM

    @profile
    def __post_init__(self) -> None:
        super(Urem, self).__post_init__()
        if self.right.min > 0:
            self.min = 0
            self.max = self.right.max - 1
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        modulus = 1 << width
        match self:
            case Urem(BValue(a), BValue(b)) if b != 0:
                return BValue(a % b % modulus, width)
            case Urem(x, BValue(0)):
                return x
            case Urem(x, BValue(1)):
                return BValue(0, width)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"
    kind: ClassVar[Kind] = Kind.BV_SHL

    @profile
    def __post_init__(self) -> None:
        super(Shl, self).__post_init__()
        if (
            isinstance(self.right, BValue)
            and self.right.value < self.width
            and (self.left.max << self.right.value <= (1 << self.width) - 1)
        ):
            self.min = min(self.left.min << self.right.value, (1 << self.width) - 1)
            self.max = min(self.left.max << self.right.value, (1 << self.width) - 1)
        elif isinstance(self.right, BValue) and self.right.value < self.width:
            self.min = 0
            self.max = min(self.left.max << self.right.value, (1 << self.width) - 1)
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        modulus = 1 << width
        match self:
            case Shl(BValue(a), BValue(b)):
                return BValue((a << b) % modulus, width)
            case Shl(x, BValue(0)):
                return x
            case Shl(x, BValue(val)) if val >= width:
                return BValue(0, width)
            case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
                return Shl(x, BValue(a + b, width))
            case Shl(Concat([x, *rest]), BValue(a)) if (
                a < self.width and a >= x.width and (len(rest) > 0)
            ):
                return Concat(
                    (
                        Shl(
                            Concat((*rest,)), BValue(a - x.width, self.width - x.width)
                        ),
                        BValue(0, x.width),
                    )
                )
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"
    kind: ClassVar[Kind] = Kind.BV_SHR

    @profile
    def __post_init__(self) -> None:
        super(Lshr, self).__post_init__()
        if isinstance(self.right, BValue):
            self.min = self.left.min >> self.right.value
            self.max = self.left.max >> self.right.value
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        modulus = 1 << width
        match self:
            case Lshr(BValue(a), BValue(b)):
                return BValue((a >> b) % modulus, width)
            case Lshr(x, BValue(0)):
                return x
            case Lshr(x, BValue(val)) if val >= width:
                return BValue(0, width)
            case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
                return Lshr(x, BValue(a + b, width))
            case Lshr(BAnd(x, y), z):
                return BAnd(Lshr(x, z), Lshr(y, z))
            case Lshr(BOr(x, y), z):
                return BOr(Lshr(x, z), Lshr(y, z))
            case Lshr(BXor(x, y), z):
                return BXor(Lshr(x, z), Lshr(y, z))
            case Lshr(Ite(c, x, y), z):
                return Ite(c, Lshr(x, z), Lshr(y, z))
            case Lshr(Concat([*rest, x]), BValue(a)) if (
                a < self.width and a >= x.width and (len(rest) > 0)
            ):
                return Concat(
                    (
                        BValue(0, x.width),
                        Lshr(
                            Concat((*rest,)), BValue(a - x.width, self.width - x.width)
                        ),
                    )
                )
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"
    kind: ClassVar[Kind] = Kind.BV_ULT

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Ult(BValue(a), BValue(b)):
                return CValue(a < b)
            case Ult(x, BValue(0)):
                return CValue(False)
            case Ult(BValue(0), x):
                return Distinct(x, BValue(0, x.width))
            case Ult(x, BValue(1)):
                return Eq(x, BValue(0, x.width))
            case Ult(x, y) if x == y:
                return CValue(False)
            case Ult(BValue(a), Concat([BValue(b) as x, *rest]) as c) if (
                b == a >> c.width - x.width and len(rest) > 0
            ):
                rwidth = c.width - x.width
                return Ult(BValue(a & (1 << rwidth) - 1, rwidth), Concat((*rest,)))
            case Ult(Concat([BValue(b) as x, *rest]) as c, BValue(a)) if (
                b == a >> c.width - x.width and len(rest) > 0
            ):
                rwidth = c.width - x.width
                return Ult(Concat((*rest,)), BValue(a & (1 << rwidth) - 1, rwidth))
            case Ult(Add(BValue(a), x), BValue(b)) if (
                a <= b and x.max < (1 << x.width) - a
            ):
                return Ult(x, BValue(b - a, x.width))
            case Ult(BValue(b), Add(BValue(a), x)) if (
                a <= b and x.max < (1 << x.width) - a
            ):
                return Ult(BValue(b - a, x.width), x)
            case Ult(Add(BValue(a), x), BValue(b)) if (
                a > b and x.min >= (1 << x.width) - a
            ):
                return Ult(x, BValue(b - a + (1 << x.width), x.width))
            case Ult(BValue(b), Add(BValue(a), x)) if (
                a > b and x.min >= (1 << x.width) - a
            ):
                return Ult(BValue(b - a + (1 << x.width), x.width), x)
            case Ult(Add(BValue(a), x), y) if x == y and a > 0:
                return Not(Ult(x, BValue((1 << x.width) - a, x.width)))
            case Ult(x, Add(BValue(a), y)) if x == y and a > 0:
                return Ult(x, BValue((1 << x.width) - a, x.width))
            case Ult(
                Add(BValue(a), x), Add(BValue(b), BAnd(BValue(c), Add(BValue(d), y)))
            ) if (
                a < b + (d - 31)
                and b < 1 << x.width
                and (c == (1 << x.width) - 32)
                and (d >= 31)
                and (x == y)
                and (x.max < (1 << x.width) - d - b)
            ):
                return CValue(True)
            case Ult(
                Add(BValue(b), BAnd(BValue(c), Add(BValue(d), y))), Add(BValue(a), x)
            ) if (
                a <= b + (d - 31)
                and b < 1 << x.width
                and (c == (1 << x.width) - 32)
                and (d >= 31)
                and (x == y)
                and (x.max < (1 << x.width) - d - b)
            ):
                return CValue(False)
            case Ult(x, y) if x.max < y.min:
                return CValue(True)
            case Ult(x, y) if y.max <= x.min:
                return CValue(False)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"
    kind: ClassVar[Kind] = Kind.BV_NAND

    @profile
    def __post_init__(self) -> None:
        super(Nand, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Nand(x, y):
                return BNot(BAnd(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"
    kind: ClassVar[Kind] = Kind.BV_NOR

    @profile
    def __post_init__(self) -> None:
        super(Nor, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Nor(x, y):
                return BNot(BOr(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    kind: ClassVar[Kind] = Kind.BV_XOR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE

    @profile
    def __post_init__(self) -> None:
        super(BXor, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case BXor(BValue(a), BValue(b)):
                return BValue(a ^ b, width)
            case BXor(BValue(0), x):
                return x
            case BXor(BValue(m), x) if m == mask:
                return BNot(x)
            case BXor(x, y) if x == y:
                return BValue(0, width)
            case BXor(x, BNot(y)) if x == y:
                return BValue(mask, width)
            case BXor(BValue(a), BXor(BValue(b), x)):
                return BXor(BValue(a ^ b, width), x)
            case BXor(Ite(c, x, y), z):
                return Ite(c, BXor(x, z), BXor(y, z))
            case BXor(z, Ite(c, x, y)):
                return Ite(c, BXor(x, z), BXor(y, z))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"
    kind: ClassVar[Kind] = Kind.BV_XNOR

    @profile
    def __post_init__(self) -> None:
        super(Xnor, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Xnor(x, y):
                return BNot(BXor(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Comp(BTerm):
    op: ClassVar[bytes] = b"bvcomp"
    kind: ClassVar[Kind] = Kind.BV_COMP
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = 1
        super(Comp, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Comp(x, y):
                return Ite(Eq(x, y), BValue(1, 1), BValue(0, 1))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"
    kind: ClassVar[Kind] = Kind.BV_SUB

    @profile
    def __post_init__(self) -> None:
        super(Sub, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Sub(x, y):
                return Add(Add(x, BNot(y)), BValue(1, self.width))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"
    kind: ClassVar[Kind] = Kind.BV_SDIV

    @profile
    def __post_init__(self) -> None:
        super(Sdiv, self).__post_init__()
        if (
            isinstance(self.right, BValue)
            and self.left.max < 1 << self.width - 1
            and (self.right.value < 1 << self.width - 1)
            and (self.right.value != 0)
        ):
            self.min = self.left.min // self.right.value
            self.max = self.left.max // self.right.value
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case Sdiv(BValue() as x, BValue(b) as y) if b != 0:
                return BValue(x.sgnd // y.sgnd, width)
            case Sdiv(x, BValue(0)):
                return Ite(
                    Sge(x, BValue(0, width)), BValue(mask, width), BValue(1, width)
                )
            case Sdiv(x, BValue(1)):
                return x
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"
    kind: ClassVar[Kind] = Kind.BV_SREM

    @profile
    def __post_init__(self) -> None:
        super(Srem, self).__post_init__()
        if (
            self.left.max < 1 << self.width - 1
            and self.right.min > 0
            and (self.right.max < 1 << self.width - 1)
        ):
            self.min = 0
            self.max = self.right.max - 1
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        match self:
            case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd > 0:
                return BValue(x.sgnd % y.sgnd, width)
            case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd < 0:
                return BValue(x.sgnd % -y.sgnd, width)
            case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd > 0:
                return BValue(-(-x.sgnd % y.sgnd), width)
            case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd < 0:
                return BValue(x.sgnd % y.sgnd, width)
            case Srem(x, BValue(0)):
                return x
            case Srem(x, BValue(1)):
                return BValue(0, width)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"
    kind: ClassVar[Kind] = Kind.BV_SMOD

    @profile
    def __post_init__(self) -> None:
        super(Smod, self).__post_init__()
        if self.right.min > 0 and self.right.max < 1 << self.width - 1:
            self.min = 0
            self.max = self.right.max - 1
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        match self:
            case Smod(BValue() as x, BValue(b) as y) if b != 0:
                return BValue(x.sgnd % y.sgnd, width)
            case Smod(x, BValue(0)):
                return x
            case Smod(x, BValue(1)):
                return BValue(0, width)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"
    kind: ClassVar[Kind] = Kind.BV_ASHR

    @profile
    def __post_init__(self) -> None:
        super(Ashr, self).__post_init__()
        if isinstance(self.right, BValue) and self.left.max < 1 << self.width - 1:
            self.min = self.left.min >> self.right.value
            self.max = self.left.max >> self.right.value
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        mask = (1 << width) - 1
        match self:
            case Ashr(BValue() as x, BValue(b)) if x.sgnd >= 0:
                return BValue(x.sgnd >> b, width)
            case Ashr(BValue(a) as x, BValue(b)) if x.sgnd < 0:
                return BValue((a ^ mask) >> b ^ mask, width)
            case Ashr(x, BValue(0)):
                return x
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"
    kind: ClassVar[Kind] = Kind.BV_REPEAT

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        self.width = self.term.width * self.i
        super(Repeat, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Repeat(1, x):
                return x
            case Repeat(i, x) if i > 1:
                return Concat((x, Repeat(i - 1, x)))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"
    kind: ClassVar[Kind] = Kind.BV_ZERO_EXTEND

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(ZeroExtend, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case ZeroExtend(0, x):
                return x
            case ZeroExtend(i, x) if i > 0:
                return Concat((BValue(0, i), x))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"
    kind: ClassVar[Kind] = Kind.BV_SIGN_EXTEND

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width + self.i
        super(SignExtend, self).__post_init__()
        if self.term.max < 1 << self.term.width - 1:
            self.min = self.term.min
            self.max = self.term.max
        else:
            self.min = 0
            self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        width = self.width
        match self:
            case SignExtend(_i, BValue() as x):
                return BValue(x.sgnd, width)
            case SignExtend(0, x):
                return x
            case SignExtend(i, SignExtend(j, x)):
                return SignExtend(i + j, x)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"
    kind: ClassVar[Kind] = Kind.BV_ROL

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateLeft, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case RotateLeft(i, x) if i % self.width == 0:
                return x
            case RotateLeft(i, x) if i % self.width != 0:
                i = i % self.width
                return Concat(
                    (
                        Extract(self.width - i - 1, 0, x),
                        Extract(self.width - 1, self.width - i, x),
                    )
                )
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"
    kind: ClassVar[Kind] = Kind.BV_ROR

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        self.width = self.term.width
        super(RotateRight, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case RotateRight(i, x) if i % self.width == 0:
                return x
            case RotateRight(i, x) if i % self.width != 0:
                i = i % self.width
                return Concat((Extract(i - 1, 0, x), Extract(self.width - 1, i, x)))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"
    kind: ClassVar[Kind] = Kind.BV_ULE

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Ule(x, y):
                return Not(Ult(y, x))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"
    kind: ClassVar[Kind] = Kind.BV_UGT

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Ugt(x, y):
                return Ult(y, x)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"
    kind: ClassVar[Kind] = Kind.BV_UGE

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Uge(x, y):
                return Not(Ult(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"
    kind: ClassVar[Kind] = Kind.BV_SLT

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Slt(BValue() as x, BValue() as y):
                return CValue(x.sgnd < y.sgnd)
            case Slt(Add(BValue(a) as p, x), BValue(b) as q) if (
                0 <= p.sgnd
                and p.sgnd <= q.sgnd
                and (x.max < (1 << x.width - 1) - q.sgnd)
            ):
                return Slt(x, BValue(b - a, x.width))
            case Slt(BValue(b) as q, Add(BValue(a) as p, x)) if (
                0 <= p.sgnd
                and p.sgnd <= q.sgnd
                and (x.max < (1 << x.width - 1) - q.sgnd)
            ):
                return Slt(BValue(b - a, x.width), x)
            case Slt(Add(BValue(a) as p, x), BValue(b)) if (
                p.sgnd < 0
                and -p.sgnd < 1 << x.width - 1
                and (b - p.sgnd < 1 << x.width - 1)
                and (x.max < 1 << x.width - 2)
            ):
                return Slt(x, BValue(b - p.sgnd, x.width))
            case Slt(BValue(b), Add(BValue(a) as p, x)) if (
                p.sgnd < 0
                and -p.sgnd < 1 << x.width - 1
                and (b - p.sgnd < 1 << x.width - 1)
                and (x.max < 1 << x.width - 2)
            ):
                return Slt(BValue(b - p.sgnd, x.width), x)
            case Slt(x, y) if x.max < 1 << x.width - 1 and y.max < 1 << x.width - 1:
                return Ult(x, y)
            case Slt(x, y) if y.max < 1 << y.width - 1 and x.min >= 1 << x.width - 1:
                return CValue(True)
            case Slt(x, y) if x.max < 1 << x.width - 1 and y.min >= 1 << y.width - 1:
                return CValue(False)
            case Slt(x, y) if x.max < y.min and x.min >= 1 << x.width - 1:
                return CValue(True)
            case Slt(x, y) if y.max <= x.min and y.min >= 1 << y.width - 1:
                return CValue(False)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"
    kind: ClassVar[Kind] = Kind.BV_SLE

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sle(x, y):
                return Not(Slt(y, x))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"
    kind: ClassVar[Kind] = Kind.BV_SGT

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sgt(x, y):
                return Slt(y, x)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"
    kind: ClassVar[Kind] = Kind.BV_SGE

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sge(x, y):
                return Not(Slt(x, y))
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        self.width = self.left.width
        super(Ite, self).__post_init__()
        self.min = min(self.left.min, self.right.min)
        self.max = max(self.left.max, self.right.max)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.cond, self.left, self.right)

    @profile
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

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Ite(CValue(True), x, _y):
                return x
            case Ite(CValue(False), _x, y):
                return y
            case Ite(_c, x, y) if x == y:
                return x
            case Ite(Not(c), x, y):
                return Ite(c, y, x)
            case Ite(c, Ite(d, x, y), z) if c == d:
                return Ite(c, x, z)
            case Ite(c, x, Ite(d, y, z)) if c == d:
                return Ite(c, x, z)
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class ATerm(BaseTerm):
    def sort(self) -> bytes:
        return b"(Array (_ BitVec %d) (_ BitVec %d))" % self.width()

    @abc.abstractmethod
    def width(self) -> tuple[int, int]: ...


@dataclass(repr=False, slots=True, eq=False)
class ASymbol(ATerm):
    name: bytes
    key: int
    value: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.value)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, self.width())


@dataclass(repr=False, slots=True, eq=False)
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.default,)

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((as const (Array (_ BitVec %d) (_ BitVec %d))) "
            % (self.key, self.default.width)
        )
        self.default.dump(ctx)
        ctx.write(b")")

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.default.bzla, self.width())


@dataclass(repr=False, slots=True, eq=False)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    kind: ClassVar[Kind] = Kind.ARRAY_SELECT
    array: ATerm
    key: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        k, v = self.array.width()
        assert k == self.key.width
        self.width = v
        if isinstance(self.array, Store):
            self.array.copied = True
        super(Select, self).__post_init__()
        self.min = 0
        self.max = (1 << self.width) - 1

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.array, self.key)

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty and self._pretty == "safe_select":
            self.array.dump(ctx)
            ctx.write(b"[")
            self.key.dump(ctx)
            ctx.write(b"]")
            return
        super(Select, self).dump(ctx)

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Select(AValue(d), _key):
                return d
            case Select(Store(base, lower, upper), key):
                for k, v in reversed(upper):
                    match Eq(k, key):
                        case CValue(True):
                            return v
                        case CValue(False):
                            continue
                        case _:
                            return self
                match key:
                    case BValue(s):
                        if s in lower:
                            return lower[s]
                        else:
                            return Select(base, key)
                    case _:
                        if not lower:
                            return Select(base, key)
                        elif upper:
                            return Select(Store(base, lower), key, recurse=False)
                        else:
                            return self
            case _:
                return self


@dataclass(repr=False, slots=True, eq=False)
class Store(ATerm):
    op: ClassVar[bytes] = b"store"
    kind: ClassVar[Kind] = Kind.ARRAY_STORE
    category: ClassVar[TermCategory] = TermCategory.MUTABLE
    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])
    copied: bool = field(init=False, default=False)

    @profile
    def __post_init__(self) -> None:
        assert not self.lower and (not self.upper)
        self._bzla = self.base.bzla
        super(Store, self).__post_init__()

    def __copy__(self) -> Self:
        return copy.deepcopy(self)

    def __deepcopy__(self, memo: Any, /) -> Self:
        k = self.__new__(self.__class__)
        k.base = self.base
        k.lower = copy.copy(self.lower)
        k.upper = copy.copy(self.upper)
        k.copied = False
        k.count = self.count
        k._bzla = self._bzla
        return k

    def width(self) -> tuple[int, int]:
        return self.base.width()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (
            self.base,
            *self.lower.values(),
            *(k for k, _ in self.upper),
            *(v for _, v in self.upper),
        )

    @profile
    def set(self, key: BTerm, value: BTerm) -> Store:
        array = copy.deepcopy(self) if self.copied else self
        array._set(key, value)
        return array

    @profile
    def _set(self, key: BTerm, value: BTerm) -> None:
        if self._bzla is not None:
            self._bzla = BZLA.mk_term(self.kind, (self._bzla, key.bzla, value.bzla))
        for i, (k, v) in reversed(tuple(enumerate(self.upper))):
            match Eq(k, key):
                case CValue(True):
                    self.upper[i] = (k, value)
                    self.count += value.count - v.count
                    return
                case CValue(False):
                    continue
                case _:
                    self.upper.append((key, value))
                    self.count += key.count + value.count + 2
                    return
        if isinstance(key, BValue):
            k = key.value
            if k in self.lower:
                self.count -= self.lower[k].count + 1
            self.lower[k] = value
            self.count += value.count + 1
        else:
            self.upper.append((key, value))
            self.count += key.count + value.count + 2

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty:
            ctx.write(b"{\n  ")
            self.base.dump(ctx)
            for k, v in self.lower.items():
                ctx.write(b"\n  " + hex(k).encode())
                ctx.write(b" -> ")
                v.dump(ctx)
            for k, v in self.upper:
                ctx.write(b"\n  ")
                k.dump(ctx)
                ctx.write(b"\n   -> ")
                v.dump(ctx)
            ctx.write(b"\n}")
        else:
            ctx.write(b"(store " * (len(self.lower) + len(self.upper)))
            self.base.dump(ctx)
            for k, v in self.lower.items():
                if self.base.key % 8 == 0:
                    ctx.write(
                        b" #x" + k.to_bytes(self.base.key // 8).hex().encode() + b" "
                    )
                else:
                    ctx.write(b" #b" + bin(k)[2:].zfill(self.base.key).encode() + b" ")
                v.dump(ctx)
                ctx.write(b")")
            for k, v in self.upper:
                ctx.write(b" ")
                k.dump(ctx)
                ctx.write(b" ")
                v.dump(ctx)
                ctx.write(b")")

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        term = self.base.bzla
        for k, v in self.lower.items():
            term = BZLA.mk_term(
                self.kind, (term, BZLA.mk_value(k, self.width()[0]), v.bzla)
            )
        for k, v in self.upper:
            term = BZLA.mk_term(self.kind, (term, k.bzla, v.bzla))
        return term
