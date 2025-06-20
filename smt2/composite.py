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
from typing import Any, ClassVar, Self, override

from .theory_core import BaseTerm, DumpContext

type MinMax = tuple[int, int]


class RewriteMeta(abc.ABCMeta):
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
        match term:
            case CTerm():
                term = constraint_reduction(term)
                term = constraint_folding(term)
                term = constraint_logic_boolean(term)
                term = constraint_logic_bitvector(term)
                term = constraint_minmax(term)
            case BTerm():
                term = bitvector_reduction(term)
                term = bitvector_folding(term)
                term = bitvector_logic_boolean(term)
                term = bitvector_logic_arithmetic(term)
                term = bitvector_logic_shifts(term)
                term = bitvector_yolo(term)
                min, max = propagate_minmax(term)
                object.__setattr__(term, "min", min)
                object.__setattr__(term, "max", max)
            case _:
                raise TypeError("unknown term", term)
        return term


@dataclass(frozen=True, repr=False, slots=True)
class CTerm(BaseTerm, metaclass=RewriteMeta):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(frozen=True, repr=False, slots=True)
class CSymbol(CTerm):
    name: bytes

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
class CValue(CTerm):
    value: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, repr=False, slots=True)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    term: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    left: CTerm
    right: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    commutative: ClassVar[bool] = True
    left: S
    right: S

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(frozen=True, repr=False, slots=True)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S

    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(frozen=True, repr=False, slots=True)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: CTerm
    right: CTerm


@dataclass(frozen=True, repr=False, slots=True)
class BTerm(BaseTerm, metaclass=RewriteMeta):
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
        if self.value < 0:
            object.__setattr__(self, "value", self.value + (1 << w))
        assert 0 <= self.value < 1 << w
        object.__setattr__(self, "width", w)

    @property
    def sgnd(self) -> int:
        if self.value & 1 << self.width - 1:
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
class Comp(BTerm):
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
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((as const (Array (_ BitVec %d) (_ BitVec %d))) "
            % (self.key, self.default.width)
        )
        self.default.dump(ctx)
        ctx.write(b")")

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, repr=False, slots=True)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    array: ATerm
    key: BTerm

    @override
    def __post_init__(self) -> None:
        BaseTerm.__post_init__(self)
        k, v = self.array.width()
        assert k == self.key.width
        object.__setattr__(self, "width", v)
        if isinstance(self.array, Store):
            object.__setattr__(self, "array", copy.deepcopy(self.array))


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
        object.__setattr__(k, "descendants", self.descendants)
        return k

    def width(self) -> tuple[int, int]:
        return self.base.width()

    def set(self, key: BTerm, value: BTerm) -> None:
        descendants = self.descendants
        if isinstance(key, BValue) and (not self.upper):
            k = key.value
            if k in self.lower:
                descendants -= self.lower[k].descendants + 1
            self.lower[k] = value
            descendants += value.descendants + 1
        else:
            self.upper.append((key, value))
            descendants += key.descendants + value.descendants + 2
        object.__setattr__(self, "descendants", descendants)

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


def constraint_reduction(term: CTerm) -> CTerm:
    match term:
        case Implies(x, y):
            return Or(y, Not(x))
        case Eq(CTerm() as x, CTerm() as y):
            return Not(Xor(x, y))
        case Distinct(CTerm() as x, CTerm() as y):
            return Xor(x, y)
        case Distinct(BTerm() as x, BTerm() as y):
            return Not(Eq(x, y))
        case CIte(c, x, y):
            return Or(And(c, x), And(Not(c), y))
        case Ugt(x, y):
            return Ult(y, x)
        case Uge(x, y):
            return Ule(y, x)
        case Sgt(x, y):
            return Slt(y, x)
        case Sge(x, y):
            return Sle(y, x)
        case _:
            return term


def constraint_folding(term: CTerm) -> CTerm:
    match term:
        case Not(CValue(a)):
            return CValue(not a)
        case And(CValue(a), CValue(b)):
            return CValue(a and b)
        case Or(CValue(a), CValue(b)):
            return CValue(a or b)
        case Xor(CValue(a), CValue(b)):
            return CValue(a != b)
        case Eq(BValue(a), BValue(b)):
            return CValue(a == b)
        case Ult(BValue(a), BValue(b)):
            return CValue(a < b)
        case Ule(BValue(a), BValue(b)):
            return CValue(a <= b)
        case Slt(BValue() as x, BValue() as y):
            return CValue(x.sgnd < y.sgnd)
        case Sle(BValue() as x, BValue() as y):
            return CValue(x.sgnd <= y.sgnd)
        case _:
            return term


def constraint_logic_boolean(term: CTerm) -> CTerm:
    match term:
        case Not(Not(inner)):
            return inner
        case And(CValue(True), x):
            return x
        case And(CValue(False), x):
            return CValue(False)
        case And(x, y) if x == y:
            return x
        case And(x, Not(y)) if x == y:
            return CValue(False)
        case Not(And(x, y)):
            return Or(Not(x), Not(y))
        case Or(CValue(True), x):
            return CValue(True)
        case Or(CValue(False), x):
            return x
        case Or(x, y) if x == y:
            return x
        case Or(x, Not(y)) if x == y:
            return CValue(True)
        case Not(Or(x, y)):
            return And(Not(x), Not(y))
        case Xor(CValue(True), x):
            return Not(x)
        case Xor(CValue(False), x):
            return x
        case Xor(x, y) if x == y:
            return CValue(False)
        case Xor(x, Not(y)) if x == y:
            return CValue(True)
        case _:
            return term


def constraint_logic_bitvector(term: CTerm) -> CTerm:
    match term:
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
        case Eq(BValue(a), Add(BValue(b), x)):
            return Eq(Add(BValue(a, x.width), Neg(BValue(b, x.width))), x)
        case Eq(BTerm() as z, Ite(c, x, y)) if z == x:
            return Or(c, Eq(z, y))
        case Eq(BTerm() as z, Ite(c, x, y)) if z == y:
            return Or(Not(c), Eq(z, x))
        case Eq(BValue(a) as v, Ite(c, BValue(p), y)) if a != p:
            return And(Not(c), Eq(v, y))
        case Eq(BValue(a) as v, Ite(c, x, BValue(q))) if a != q:
            return And(c, Eq(v, x))
        case Eq(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
            return And(
                Eq(Concat((*rest,)), BValue(a >> x.width, c.width - x.width)),
                Eq(BValue(a & (1 << x.width) - 1, x.width), x),
            )
        case Eq(Concat([*rest, x]), Ite(c, p, q) as z) if len(rest) > 0:
            return And(
                Eq(
                    Concat((*rest,)),
                    Ite(
                        c,
                        Extract(z.width - 1, x.width, p),
                        Extract(z.width - 1, x.width, q),
                    ),
                ),
                Eq(x, Ite(c, Extract(x.width - 1, 0, p), Extract(x.width - 1, 0, q))),
            )
        case Eq(Concat([x, *xx]), Concat([y, *yy])) if (
            x.width == y.width and len(xx) > 0 and (len(yy) > 0)
        ):
            return And(Eq(x, y), Eq(Concat((*xx,)), Concat((*yy,))))
        case Eq(Concat([*xx, x]), Concat([*yy, y])) if (
            x.width == y.width and len(xx) > 0 and (len(yy) > 0)
        ):
            return And(Eq(Concat((*xx,)), Concat((*yy,))), Eq(x, y))
        case Ult(x, BValue(0)):
            return CValue(False)
        case Ule(x, BValue(0)):
            return Eq(x, BValue(0, x.width))
        case Ult(BValue(0), x):
            return Distinct(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            return CValue(True)
        case Ult(x, BValue(1)):
            return Eq(x, BValue(0, x.width))
        case Ult(x, y) if x == y:
            return CValue(False)
        case Ule(x, y) if x == y:
            return CValue(True)
        case Not(Ult(x, y)):
            return Ule(y, x)
        case Not(Ule(x, y)):
            return Ult(y, x)
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
        case _:
            return term


def bitvector_reduction(term: BTerm) -> BTerm:
    match term:
        case Neg(x):
            return Add(BValue(1, term.width), BNot(x))
        case Nand(x, y):
            return BNot(BAnd(x, y))
        case Nor(x, y):
            return BNot(BOr(x, y))
        case Xnor(x, y):
            return BNot(BXor(x, y))
        case Comp(x, y):
            return Ite(Eq(x, y), BValue(1, 1), BValue(0, 1))
        case Sub(x, y):
            return Add(Add(x, BNot(y)), BValue(1, term.width))
        case Repeat(1, x):
            return x
        case Repeat(i, x) if i > 1:
            return Concat((x, Repeat(i - 1, x)))
        case ZeroExtend(0, x):
            return x
        case ZeroExtend(i, x) if i > 0:
            return Concat((BValue(0, i), x))
        case RotateLeft(i, x) if i % term.width == 0:
            return x
        case RotateLeft(i, x) if i % term.width != 0:
            i = i % term.width
            return Concat(
                (
                    Extract(term.width - i - 1, 0, x),
                    Extract(term.width - 1, term.width - i, x),
                )
            )
        case RotateRight(i, x) if i % term.width == 0:
            return x
        case RotateRight(i, x) if i % term.width != 0:
            i = i % term.width
            return Concat((Extract(i - 1, 0, x), Extract(term.width - 1, i, x)))
        case _:
            return term


def bitvector_folding(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Concat([single]):
            return single
        case Concat([BValue(a) as x, BValue(b) as y, *rest]):
            return Concat((BValue(a << y.width | b, x.width + y.width), *rest))
        case Concat([*rest, BValue(a) as x, BValue(b) as y]):
            return Concat((*rest, BValue(a << y.width | b, x.width + y.width)))
        case Extract(i, j, BValue(a)):
            return BValue(a >> j & (1 << i - j + 1) - 1, i - j + 1)
        case BNot(BValue(a)):
            return BValue(a ^ mask, width)
        case BAnd(BValue(a), BValue(b)):
            return BValue(a & b, width)
        case BOr(BValue(a), BValue(b)):
            return BValue(a | b, width)
        case BXor(BValue(a), BValue(b)):
            return BValue(a ^ b, width)
        case Add(BValue(a), BValue(b)):
            return BValue((a + b) % modulus, width)
        case Mul(BValue(a), BValue(b)):
            return BValue(a * b % modulus, width)
        case Udiv(BValue(a), BValue(b)) if b != 0:
            return BValue(a // b, width)
        case Urem(BValue(a), BValue(b)) if b != 0:
            return BValue(a % b % modulus, width)
        case Shl(BValue(a), BValue(b)):
            return BValue((a << b) % modulus, width)
        case Lshr(BValue(a), BValue(b)):
            return BValue((a >> b) % modulus, width)
        case Sdiv(BValue() as x, BValue(b) as y) if b != 0:
            return BValue(x.sgnd // y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd > 0:
            return BValue(x.sgnd % y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd >= 0 and y.sgnd < 0:
            return BValue(x.sgnd % -y.sgnd, width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd > 0:
            return BValue(-(-x.sgnd % y.sgnd), width)
        case Srem(BValue() as x, BValue() as y) if x.sgnd < 0 and y.sgnd < 0:
            return BValue(x.sgnd % y.sgnd, width)
        case Smod(BValue() as x, BValue(b) as y) if b != 0:
            return BValue(x.sgnd % y.sgnd, width)
        case Ashr(BValue() as x, BValue(b)) if x.sgnd >= 0:
            return BValue(x.sgnd >> b, width)
        case Ashr(BValue(a) as x, BValue(b)) if x.sgnd < 0:
            return BValue((a ^ mask) >> b ^ mask, width)
        case SignExtend(_i, BValue() as x):
            return BValue(x.sgnd, width)
        case Ite(CValue(True), x, _y):
            return x
        case Ite(CValue(False), _x, y):
            return y
        case _:
            return term


def bitvector_logic_boolean(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    match term:
        case BNot(BNot(inner)):
            return inner
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
        case _:
            return term


def bitvector_logic_arithmetic(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case BNot(Add(x, y)):
            return Add(BValue(1, width), Add(BNot(x), BNot(y)))
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
        case Mul(BValue(0), x):
            return BValue(0, width)
        case Mul(BValue(1), x):
            return x
        case Udiv(x, BValue(0)):
            return BValue(mask, width)
        case Udiv(x, BValue(1)):
            return x
        case Sdiv(x, BValue(0)):
            return Ite(Sge(x, BValue(0, width)), BValue(mask, width), BValue(1, width))
        case Sdiv(x, BValue(1)):
            return x
        case Urem(x, BValue(0)):
            return x
        case Urem(x, BValue(1)):
            return BValue(0, width)
        case Srem(x, BValue(0)):
            return x
        case Srem(x, BValue(1)):
            return BValue(0, width)
        case Smod(x, BValue(0)):
            return x
        case Smod(x, BValue(1)):
            return BValue(0, width)
        case _:
            return term


def bitvector_logic_shifts(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    match term:
        case Shl(x, BValue(0)):
            return x
        case Shl(x, BValue(val)) if val >= width:
            return BValue(0, width)
        case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
            return Shl(x, BValue(a + b, width))
        case Lshr(x, BValue(0)):
            return x
        case Lshr(x, BValue(val)) if val >= width:
            return BValue(0, width)
        case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
            return Lshr(x, BValue(a + b, width))
        case Ashr(x, BValue(0)):
            return x
        case SignExtend(0, x):
            return x
        case SignExtend(i, SignExtend(j, x)):
            return SignExtend(i + j, x)
        case Concat([*left, Concat([*right])]) | Concat([Concat([*left]), *right]):
            return Concat((*left, *right))
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
        case Ite(_c, x, y) if x == y:
            return x
        case Ite(Not(c), x, y):
            return Ite(c, y, x)
        case Ite(c, Ite(d, x, y), z) if c == d:
            return Ite(c, x, z)
        case Ite(c, x, Ite(d, y, z)) if c == d:
            return Ite(c, x, z)
        case BNot(Ite(c, x, y)):
            return Ite(c, BNot(x), BNot(y))
        case BAnd(Ite(c, x, y), z) | BAnd(z, Ite(c, x, y)):
            return Ite(c, BAnd(x, z), BAnd(y, z))
        case BOr(Ite(c, x, y), z) | BOr(z, Ite(c, x, y)):
            return Ite(c, BOr(x, z), BOr(y, z))
        case BXor(Ite(c, x, y), z) | BXor(z, Ite(c, x, y)):
            return Ite(c, BXor(x, z), BXor(y, z))
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
        case BAnd(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
            mask = (1 << x.width) - 1
            return Concat(
                (
                    BAnd(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                    BAnd(BValue(a & mask, x.width), x),
                )
            )
        case BOr(BValue(a), Concat([*rest, x]) as c) if len(rest) > 0:
            mask = (1 << x.width) - 1
            return Concat(
                (
                    BOr(BValue(a >> x.width, c.width - x.width), Concat((*rest,))),
                    BOr(BValue(a & mask, x.width), x),
                )
            )
        case Shl(Concat([x, *rest]), BValue(a)) if (
            a < term.width and a >= x.width and (len(rest) > 0)
        ):
            return Concat(
                (
                    Shl(Concat((*rest,)), BValue(a - x.width, term.width - x.width)),
                    BValue(0, x.width),
                )
            )
        case Lshr(Concat([*rest, x]), BValue(a)) if (
            a < term.width and a >= x.width and (len(rest) > 0)
        ):
            return Concat(
                (
                    BValue(0, x.width),
                    Lshr(Concat((*rest,)), BValue(a - x.width, term.width - x.width)),
                )
            )
        case _:
            return term


def bitvector_yolo(term: BTerm) -> BTerm:
    match term:
        case Extract(i, j, Lshr(x, BValue(shift))) if i < x.width - shift:
            return Extract(i + shift, j + shift, x)
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
                        return term
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
                        return term
        case _:
            return term


def propagate_minmax(term: BTerm) -> MinMax:
    mask = (1 << term.width) - 1
    slimit = 1 << term.width - 1
    match term:
        case BValue(a):
            return (a, a)
        case Concat([BValue(a), x]):
            return (x.min | a << x.width, x.max | a << x.width)
        case BNot(x):
            return (x.max ^ mask, x.min ^ mask)
        case BAnd(x, y):
            return (0, min(x.max, y.max))
        case BOr(x, y):
            return (max(x.min, y.min), mask)
        case Add(x, y) if x.max < slimit and y.max < slimit:
            return (x.min + y.min, x.max + y.max)
        case Add(BValue() as x, y) if x.sgnd < 0 and y.min + x.sgnd > 0:
            return (y.min + x.sgnd, y.max + x.sgnd)
        case Mul(BValue(a), y) if a * y.max <= mask:
            return (a * y.min, a * y.max)
        case Udiv(x, BValue(a)) if a != 0:
            return (x.min // a, x.max // a)
        case Urem(_, y) if y.min > 0:
            return (0, y.max - 1)
        case Shl(x, BValue(a)) if a < term.width and x.max << a <= mask:
            return (min(x.min << a, mask), min(x.max << a, mask))
        case Shl(x, BValue(a)) if a < term.width:
            return (0, min(x.max << a, mask))
        case Lshr(x, BValue(a)):
            return (x.min >> a, x.max >> a)
        case Sdiv(x, BValue(a)) if x.max < slimit and a < slimit and (a != 0):
            return (x.min // a, x.max // a)
        case Srem(x, y) if x.max < slimit and y.min > 0 and (y.max < slimit):
            return (0, y.max - 1)
        case Smod(_, y) if y.min > 0 and y.max < slimit:
            return (0, y.max - 1)
        case Ashr(x, BValue(a)) if x.max < slimit:
            return (x.min >> a, x.max >> a)
        case SignExtend(_i, x) if x.max < 1 << x.width - 1:
            return (x.min, x.max)
        case Ite(_, x, y):
            return (min(x.min, y.min), max(x.max, y.max))
        case _:
            return (0, mask)


def constraint_minmax(term: CTerm) -> CTerm:
    match term:
        case Eq(BTerm() as x, BTerm() as y) if x.max < y.min:
            return CValue(False)
        case Eq(BTerm() as x, BTerm() as y) if y.max < x.min:
            return CValue(False)
        case Ult(x, y) if x.max < y.min:
            return CValue(True)
        case Ult(x, y) if y.max <= x.min:
            return CValue(False)
        case Ule(x, y) if x.max <= y.min:
            return CValue(True)
        case Ule(x, y) if y.max < x.min:
            return CValue(False)
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
            return term
