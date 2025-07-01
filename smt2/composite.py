"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analyze_composite

"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
import copy
from dataclasses import InitVar, dataclass, field
from functools import reduce
from line_profiler import profile
from typing import Any, ClassVar, Self, override

from .theory_core import BaseTerm, DumpContext

type MinMax = tuple[int, int]


class RewriteMeta(abc.ABCMeta):
    @profile
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        assert issubclass(self, BaseTerm)
        if self.commutative:
            match args:
                case [x, CValue() as y] if not isinstance(x, CValue):
                    args = (y, x)
                case [Not() as x, y] if not isinstance(y, Not):
                    args = (y, x)
                case [x, BValue() as y] if not isinstance(x, BValue):
                    args = (y, x)
                case [BNot() as x, y] if not isinstance(y, BNot):
                    args = (y, x)
                case _:
                    pass
        term = super(RewriteMeta, self).__call__(*args, **kwds)
        return term.rewrite()


@dataclass(frozen=True, repr=False, slots=True)
class CTerm(BaseTerm, metaclass=RewriteMeta):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(frozen=True, repr=False, slots=True)
class CSymbol(CTerm):
    name: bytes

    @profile
    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


@dataclass(frozen=True, repr=False, slots=True)
class CValue(CTerm):
    value: bool

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, repr=False, slots=True)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    term: CTerm

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
            case Not(Ult(x, y)):
                return Ule(y, x)
            case Not(Ule(x, y)):
                return Ult(y, x)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    left: CTerm
    right: CTerm

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Implies(x, y):
                return Or(y, Not(x))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

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


@dataclass(frozen=True, repr=False, slots=True)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

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


@dataclass(frozen=True, repr=False, slots=True)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

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


@dataclass(frozen=True, repr=False, slots=True)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    commutative: ClassVar[bool] = True
    left: S
    right: S

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
            case Eq(BTerm() as z, Ite(c, x, y)) if z == x:
                return Or(c, Eq(z, y))
            case Eq(BTerm() as z, Ite(c, x, y)) if z == y:
                return Or(Not(c), Eq(z, x))
            case Eq(BValue(a) as v, Ite(c, BValue(p), y)) if a != p:
                return And(Not(c), Eq(v, y))
            case Eq(BValue(a) as v, Ite(c, x, BValue(q))) if a != q:
                return And(c, Eq(v, x))
            case Eq(BTerm() as x, BTerm() as y) if x.max < y.min:
                return CValue(False)
            case Eq(BTerm() as x, BTerm() as y) if y.max < x.min:
                return CValue(False)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S

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


@dataclass(frozen=True, repr=False, slots=True)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: CTerm
    right: CTerm

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case CIte(c, x, y):
                return Or(And(c, x), And(Not(c), y))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class BTerm(BaseTerm, metaclass=RewriteMeta):
    width: int = field(init=False)
    min: int = field(init=False, compare=False)
    max: int = field(init=False, compare=False)

    def sort(self) -> bytes:
        return b"(_ BitVec %d)" % self.width

    @profile
    def __post_init__(self) -> None:
        super(BTerm, self).__post_init__()
        object.__setattr__(self, "min", 0)
        object.__setattr__(self, "max", (1 << self.width) - 1)


@dataclass(frozen=True, repr=False, slots=True)
class BSymbol(BTerm):
    name: bytes
    w: InitVar[int]

    @profile
    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        object.__setattr__(self, "width", w)
        super(BSymbol, self).__post_init__()

    @profile
    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


@dataclass(frozen=True, repr=False, slots=True)
class BValue(BTerm):
    value: int
    w: InitVar[int]

    @profile
    @override
    def __post_init__(self, w: int) -> None:
        assert w > 0, "width must be positive"
        if self.value < 0:
            object.__setattr__(self, "value", self.value + (1 << w))
        assert 0 <= self.value < 1 << w
        object.__setattr__(self, "width", w)
        super(BValue, self).__post_init__()
        object.__setattr__(self, "min", self.value)
        object.__setattr__(self, "max", self.value)

    @property
    @profile
    def sgnd(self) -> int:
        if self.value & 1 << self.width - 1:
            return self.value - (1 << self.width)
        return self.value

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, repr=False, slots=True)
class UnaryOp(BTerm):
    term: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.term.width)
        super(UnaryOp, self).__post_init__()


@dataclass(frozen=True, repr=False, slots=True)
class BinaryOp(BTerm):
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)
        super(BinaryOp, self).__post_init__()


@dataclass(frozen=True, repr=False, slots=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        super(CompareOp, self).__post_init__()


@dataclass(frozen=True, repr=False, slots=True)
class SingleParamOp(BTerm):
    i: int
    term: BTerm


@dataclass(frozen=True, repr=False, slots=True)
class Concat(BTerm):
    op: ClassVar[bytes] = b"concat"
    terms: tuple[BTerm, ...]

    @profile
    @override
    def __post_init__(self) -> None:
        assert len(self.terms) > 0, "width must be positive"
        w = reduce(lambda p, q: p + q.width, self.terms, 0)
        object.__setattr__(self, "width", w)
        super(Concat, self).__post_init__()
        count = reduce(int.__add__, (t.count + 1 for t in self.terms))
        object.__setattr__(self, "count", count)
        if len(self.terms) == 2 and isinstance(self.terms[0], BValue):
            object.__setattr__(
                self,
                "min",
                self.terms[1].min | self.terms[0].value << self.terms[1].width,
            )
            object.__setattr__(
                self,
                "max",
                self.terms[1].max | self.terms[0].value << self.terms[1].width,
            )

    @profile
    @override
    def walk(self, ctx: DumpContext) -> None:
        if ctx.visit(self):
            return
        for term in self.terms:
            term.walk(ctx)

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.try_alias(self):
            return
        if len(self.terms) == 1:
            self.terms[0].dump(ctx)
        else:
            ctx.write(b"(concat")
            for term in self.terms:
                ctx.write(b" ")
                term.dump(ctx)
            ctx.write(b")")

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


@dataclass(frozen=True, repr=False, slots=True)
class Extract(BTerm):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        w = self.i - self.j + 1
        object.__setattr__(self, "width", w)
        super(Extract, self).__post_init__()

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


@dataclass(frozen=True, repr=False, slots=True)
class BNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"

    @profile
    def __post_init__(self) -> None:
        super(BNot, self).__post_init__()
        object.__setattr__(self, "min", self.term.max ^ (1 << self.width) - 1)
        object.__setattr__(self, "max", self.term.min ^ (1 << self.width) - 1)

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


@dataclass(frozen=True, repr=False, slots=True)
class BAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"
    commutative: ClassVar[bool] = True

    @profile
    def __post_init__(self) -> None:
        super(BAnd, self).__post_init__()
        object.__setattr__(self, "min", 0)
        object.__setattr__(self, "max", min(self.left.max, self.right.max))

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


@dataclass(frozen=True, repr=False, slots=True)
class BOr(BinaryOp):
    op: ClassVar[bytes] = b"bvor"
    commutative: ClassVar[bool] = True

    @profile
    def __post_init__(self) -> None:
        super(BOr, self).__post_init__()
        object.__setattr__(self, "min", max(self.left.min, self.right.min))
        object.__setattr__(self, "max", (1 << self.width) - 1)

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


@dataclass(frozen=True, repr=False, slots=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Neg(x):
                return Add(BValue(1, self.width), BNot(x))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"
    commutative: ClassVar[bool] = True

    @profile
    def __post_init__(self) -> None:
        super(Add, self).__post_init__()
        if self.left.max < 1 << self.width - 1 and self.right.max < 1 << self.width - 1:
            object.__setattr__(self, "min", self.left.min + self.right.min)
            object.__setattr__(self, "max", self.left.max + self.right.max)
        elif (
            isinstance(self.left, BValue)
            and self.left.sgnd < 0
            and (self.right.min + self.left.sgnd > 0)
        ):
            object.__setattr__(self, "min", self.right.min + self.left.sgnd)
            object.__setattr__(self, "max", self.right.max + self.left.sgnd)

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
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"
    commutative: ClassVar[bool] = True

    @profile
    def __post_init__(self) -> None:
        super(Mul, self).__post_init__()
        if (
            isinstance(self.left, BValue)
            and self.left.value * self.right.max <= (1 << self.width) - 1
        ):
            object.__setattr__(self, "min", self.left.value * self.right.min)
            object.__setattr__(self, "max", self.left.value * self.right.max)

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


@dataclass(frozen=True, repr=False, slots=True)
class Udiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"

    @profile
    def __post_init__(self) -> None:
        super(Udiv, self).__post_init__()
        if isinstance(self.right, BValue) and self.right.value != 0:
            object.__setattr__(self, "min", self.left.min // self.right.value)
            object.__setattr__(self, "max", self.left.max // self.right.value)

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


@dataclass(frozen=True, repr=False, slots=True)
class Urem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"

    @profile
    def __post_init__(self) -> None:
        super(Urem, self).__post_init__()
        if self.right.min > 0:
            object.__setattr__(self, "min", 0)
            object.__setattr__(self, "max", self.right.max - 1)

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


@dataclass(frozen=True, repr=False, slots=True)
class Shl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"

    @profile
    def __post_init__(self) -> None:
        super(Shl, self).__post_init__()
        if (
            isinstance(self.right, BValue)
            and self.right.value < self.width
            and (self.left.max << self.right.value <= (1 << self.width) - 1)
        ):
            object.__setattr__(
                self,
                "min",
                min(self.left.min << self.right.value, (1 << self.width) - 1),
            )
            object.__setattr__(
                self,
                "max",
                min(self.left.max << self.right.value, (1 << self.width) - 1),
            )
        elif isinstance(self.right, BValue) and self.right.value < self.width:
            object.__setattr__(self, "min", 0)
            object.__setattr__(
                self,
                "max",
                min(self.left.max << self.right.value, (1 << self.width) - 1),
            )

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


@dataclass(frozen=True, repr=False, slots=True)
class Lshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"

    @profile
    def __post_init__(self) -> None:
        super(Lshr, self).__post_init__()
        if isinstance(self.right, BValue):
            object.__setattr__(self, "min", self.left.min >> self.right.value)
            object.__setattr__(self, "max", self.left.max >> self.right.value)

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


@dataclass(frozen=True, repr=False, slots=True)
class Ult(CompareOp):
    op: ClassVar[bytes] = b"bvult"

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
            case Ult(x, y) if x.max < y.min:
                return CValue(True)
            case Ult(x, y) if y.max <= x.min:
                return CValue(False)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Nand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Nand(x, y):
                return BNot(BAnd(x, y))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Nor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Nor(x, y):
                return BNot(BOr(x, y))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class BXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"
    commutative: ClassVar[bool] = True

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


@dataclass(frozen=True, repr=False, slots=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Xnor(x, y):
                return BNot(BXor(x, y))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Comp(BTerm):
    op: ClassVar[bytes] = b"bvcomp"
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", 1)
        super(Comp, self).__post_init__()

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Comp(x, y):
                return Ite(Eq(x, y), BValue(1, 1), BValue(0, 1))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Sub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"

    @profile
    @override
    def rewrite(self) -> BTerm:
        match self:
            case Sub(x, y):
                return Add(Add(x, BNot(y)), BValue(1, self.width))
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Sdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"

    @profile
    def __post_init__(self) -> None:
        super(Sdiv, self).__post_init__()
        if (
            isinstance(self.right, BValue)
            and self.left.max < 1 << self.width - 1
            and (self.right.value < 1 << self.width - 1)
            and (self.right.value != 0)
        ):
            object.__setattr__(self, "min", self.left.min // self.right.value)
            object.__setattr__(self, "max", self.left.max // self.right.value)

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


@dataclass(frozen=True, repr=False, slots=True)
class Srem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"

    @profile
    def __post_init__(self) -> None:
        super(Srem, self).__post_init__()
        if (
            self.left.max < 1 << self.width - 1
            and self.right.min > 0
            and (self.right.max < 1 << self.width - 1)
        ):
            object.__setattr__(self, "min", 0)
            object.__setattr__(self, "max", self.right.max - 1)

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


@dataclass(frozen=True, repr=False, slots=True)
class Smod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"

    @profile
    def __post_init__(self) -> None:
        super(Smod, self).__post_init__()
        if self.right.min > 0 and self.right.max < 1 << self.width - 1:
            object.__setattr__(self, "min", 0)
            object.__setattr__(self, "max", self.right.max - 1)

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


@dataclass(frozen=True, repr=False, slots=True)
class Ashr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"

    @profile
    def __post_init__(self) -> None:
        super(Ashr, self).__post_init__()
        if isinstance(self.right, BValue) and self.left.max < 1 << self.width - 1:
            object.__setattr__(self, "min", self.left.min >> self.right.value)
            object.__setattr__(self, "max", self.left.max >> self.right.value)

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


@dataclass(frozen=True, repr=False, slots=True)
class Repeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)
        super(Repeat, self).__post_init__()

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


@dataclass(frozen=True, repr=False, slots=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)
        super(ZeroExtend, self).__post_init__()

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


@dataclass(frozen=True, repr=False, slots=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)
        super(SignExtend, self).__post_init__()
        if self.term.max < 1 << self.term.width - 1:
            object.__setattr__(self, "min", self.term.min)
            object.__setattr__(self, "max", self.term.max)

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


@dataclass(frozen=True, repr=False, slots=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)
        super(RotateLeft, self).__post_init__()

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


@dataclass(frozen=True, repr=False, slots=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        object.__setattr__(self, "width", self.term.width)
        super(RotateRight, self).__post_init__()

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


@dataclass(frozen=True, repr=False, slots=True)
class Ule(CompareOp):
    op: ClassVar[bytes] = b"bvule"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Ule(BValue(a), BValue(b)):
                return CValue(a <= b)
            case Ule(x, BValue(0)):
                return Eq(x, BValue(0, x.width))
            case Ule(BValue(0), x):
                return CValue(True)
            case Ule(x, y) if x == y:
                return CValue(True)
            case Ule(BValue(a), Concat([BValue(b) as x, *rest]) as c) if (
                b == a >> c.width - x.width and len(rest) > 0
            ):
                rwidth = c.width - x.width
                return Ule(BValue(a & (1 << rwidth) - 1, rwidth), Concat((*rest,)))
            case Ule(Concat([BValue(b) as x, *rest]) as c, BValue(a)) if (
                b == a >> c.width - x.width and len(rest) > 0
            ):
                rwidth = c.width - x.width
                return Ule(Concat((*rest,)), BValue(a & (1 << rwidth) - 1, rwidth))
            case Ule(x, y) if x.max <= y.min:
                return CValue(True)
            case Ule(x, y) if y.max < x.min:
                return CValue(False)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Ugt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Ugt(x, y):
                return Ult(y, x)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Uge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Uge(x, y):
                return Ule(y, x)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Slt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Slt(BValue() as x, BValue() as y):
                return CValue(x.sgnd < y.sgnd)
            case Slt(x, y) if x.max < y.min and y.max < 1 << y.width - 1:
                return CValue(True)
            case Slt(x, y) if y.max <= x.min and x.max < 1 << x.width - 1:
                return CValue(False)
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


@dataclass(frozen=True, repr=False, slots=True)
class Sle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sle(BValue() as x, BValue() as y):
                return CValue(x.sgnd <= y.sgnd)
            case Sle(x, y) if x.max <= y.min and y.max < 1 << y.width - 1:
                return CValue(True)
            case Sle(x, y) if y.max < x.min and x.max < 1 << x.width - 1:
                return CValue(False)
            case Sle(x, y) if y.max < 1 << y.width - 1 and x.min >= 1 << x.width - 1:
                return CValue(True)
            case Sle(x, y) if x.max < 1 << x.width - 1 and y.min >= 1 << y.width - 1:
                return CValue(False)
            case Sle(x, y) if x.max <= y.min and x.min >= 1 << x.width - 1:
                return CValue(True)
            case Sle(x, y) if y.max < x.min and y.min >= 1 << y.width - 1:
                return CValue(False)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Sgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sgt(x, y):
                return Slt(y, x)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Sge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"

    @profile
    @override
    def rewrite(self) -> CTerm:
        match self:
            case Sge(x, y):
                return Sle(y, x)
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Ite(BTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: BTerm
    right: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        assert self.left.width == self.right.width
        object.__setattr__(self, "width", self.left.width)
        super(Ite, self).__post_init__()
        object.__setattr__(self, "min", min(self.left.min, self.right.min))
        object.__setattr__(self, "max", max(self.left.max, self.right.max))

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


@dataclass(frozen=True, repr=False, slots=True)
class ATerm(BaseTerm):
    def sort(self) -> bytes:
        return b"(Array (_ BitVec %d) (_ BitVec %d))" % self.width()

    @abc.abstractmethod
    def width(self) -> tuple[int, int]: ...


@dataclass(frozen=True, repr=False, slots=True)
class ASymbol(ATerm):
    name: bytes
    key: int
    value: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.value)

    @profile
    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @profile
    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


@dataclass(frozen=True, repr=False, slots=True)
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

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


@dataclass(frozen=True, repr=False, slots=True)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    array: ATerm
    key: BTerm

    @profile
    @override
    def __post_init__(self) -> None:
        k, v = self.array.width()
        assert k == self.key.width
        object.__setattr__(self, "width", v)
        if isinstance(self.array, Store):
            object.__setattr__(self, "array", copy.deepcopy(self.array))
        super(Select, self).__post_init__()

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
                        if upper:
                            return Select(Store(base, copy.copy(lower)), key)
                        else:
                            return self
            case _:
                return self


@dataclass(frozen=True, repr=False, slots=True)
class Store(ATerm):
    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])

    def __copy__(self) -> Self:
        return copy.deepcopy(self)

    def __deepcopy__(self, memo: Any, /) -> Self:
        k = self.__new__(self.__class__)
        object.__setattr__(k, "base", self.base)
        object.__setattr__(k, "lower", copy.copy(self.lower))
        object.__setattr__(k, "upper", copy.copy(self.upper))
        object.__setattr__(k, "count", self.count)
        return k

    def width(self) -> tuple[int, int]:
        return self.base.width()

    @profile
    def set(self, key: BTerm, value: BTerm) -> None:
        count = self.count
        if isinstance(key, BValue) and (not self.upper):
            k = key.value
            if k in self.lower:
                count -= self.lower[k].count + 1
            self.lower[k] = value
            count += value.count + 1
        else:
            self.upper.append((key, value))
            count += key.count + value.count + 2
        object.__setattr__(self, "count", count)

    @profile
    @override
    def walk(self, ctx: DumpContext) -> None:
        if ctx.visit(self):
            return
        self.base.walk(ctx)
        for term in self.lower.values():
            term.walk(ctx)
        for key, value in self.upper:
            key.walk(ctx)
            value.walk(ctx)

    @profile
    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.try_alias(self):
            return
        ctx.write(b"(store " * (len(self.lower) + len(self.upper)))
        self.base.dump(ctx)
        for k, v in self.lower.items():
            if self.base.key % 8 == 0:
                ctx.write(b" #x" + k.to_bytes(self.base.key // 8).hex().encode() + b" ")
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
