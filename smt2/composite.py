"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analysis

"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, cast, override

from .theory_core import BaseTerm, DumpContext, SortException


class RewriteMeta(abc.ABCMeta):
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        assert issubclass(self, BaseTerm)
        if self.commutative:
            match args:
                case (x, CValue() as y) if not isinstance(x, CValue):
                    args = (y, x)
                case (Not() as x, y) if not isinstance(y, Not):
                    args = (y, x)
                case (x, BValue() as y) if not isinstance(x, BValue):
                    args = (y, x)
                case (BNot() as x, y) if not isinstance(y, BNot):
                    args = (y, x)
                case _:
                    pass
        term = super(RewriteMeta, self).__call__(*args, **kwds)
        match term:
            case CTerm():
                term = constraint_reduction(term)
                term = constraint_folding(term)
                return constraint_logic(term)
            case BTerm():
                term = bitvector_reduction(term)
                term = bitvector_folding(term)
                term = bitvector_logic(term)
                return bitvector_yolo(term)
            case _:
                raise TypeError("unknown term", term)


@dataclass(frozen=True, slots=True)
class CTerm(BaseTerm, metaclass=RewriteMeta):
    def check(self, partner: BaseTerm) -> None:
        if not isinstance(partner, CTerm):
            raise SortException(self.__class__, partner.__class__)


@dataclass(frozen=True, slots=True)
class CSymbol(CTerm):
    name: bytes

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.out.extend(self.name)


@dataclass(frozen=True, slots=True)
class CValue(CTerm):
    value: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.out.extend(b"true" if self.value else b"false")


@dataclass(frozen=True, slots=True)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    term: CTerm


@dataclass(frozen=True, slots=True)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    left: CTerm
    right: CTerm


@dataclass(frozen=True, slots=True)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, slots=True)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, slots=True)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm


@dataclass(frozen=True, slots=True)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    commutative: ClassVar[bool] = True
    left: S
    right: S

    def __post_init__(self) -> None:
        self.left.check(self.right)


@dataclass(frozen=True, slots=True)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S

    def __post_init__(self) -> None:
        self.left.check(self.right)


@dataclass(frozen=True, slots=True)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    cond: CTerm
    left: CTerm
    right: CTerm


@dataclass(frozen=True, slots=True)
class BTerm(BaseTerm, metaclass=RewriteMeta):
    width: int = field(init=False)

    def check(self, partner: BaseTerm) -> None:
        if not isinstance(partner, BTerm):
            raise SortException(self.__class__, partner.__class__)
        elif self.width != partner.width:
            raise SortException(self.width, partner.width)

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
        if self.value < 0:
            object.__setattr__(self, "value", self.value + (1 << w))
        assert 0 <= self.value < (1 << w)
        object.__setattr__(self, "width", w)

    @property
    def sgnd(self) -> int:
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
        self.left.check(self.right)
        object.__setattr__(self, "width", self.left.width)


@dataclass(frozen=True, slots=True)
class CompareOp(CTerm):
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        self.left.check(self.right)


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
class Comp(BTerm):
    op: ClassVar[bytes] = b"bvcomp"
    left: BTerm
    right: BTerm

    def __post_init__(self) -> None:
        self.left.check(self.right)
        object.__setattr__(self, "width", 1)


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
        object.__setattr__(self, "width", self.term.width)


@dataclass(frozen=True, slots=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"

    def __post_init__(self) -> None:
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
        self.left.check(self.right)
        object.__setattr__(self, "width", self.left.width)


@dataclass(frozen=True, slots=True)
class ATerm(BaseTerm):
    def check(self, partner: BaseTerm) -> None:
        if not isinstance(partner, ATerm):
            raise SortException(self.__class__, partner.__class__)
        elif self.width() != partner.width():
            raise SortException(self.width(), partner.width())

    @abc.abstractmethod
    def width(self) -> tuple[int, int]: ...


@dataclass(frozen=True, slots=True)
class ASymbol(ATerm):
    name: bytes
    key: int
    value: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.value)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (
                b"(declare-fun %s () (Array (_ BitVec %d) (_ BitVec %d)))"
                % (self.name, self.key, self.value)
            ),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((_ as const (Array (_ BitVec %d) (_ BitVec %d))) "
            % (self.key, self.default.width)
        )
        self.default.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    array: ATerm
    key: BTerm

    @override
    def __post_init__(self) -> None:
        _, v = self.array.width()
        object.__setattr__(self, "width", v)


@dataclass(frozen=True, slots=True)
class Store(ATerm):
    base: ASymbol | AValue
    lower: frozenset[tuple[int, BTerm]] = frozenset()
    upper: tuple[tuple[BTerm, BTerm], ...] = ()

    def width(self) -> tuple[int, int]:
        return self.base.width()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[BTerm, BTerm]](
            [(BValue(k, self.base.key), v) for k, v in self.lower]
        )
        writes.extend(self.upper)
        ctx.write(b"(store " * len(writes))
        self.base.dump(ctx)
        for k, v in writes:
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
        case term:
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
        case term:
            return term


def constraint_logic(term: CTerm) -> CTerm:
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
        case Or(CValue(True), x):
            return CValue(True)
        case Or(CValue(False), x):
            return x
        case Or(x, y) if x == y:
            return x
        case Or(x, Not(y)) if x == y:
            return CValue(True)
        case Xor(CValue(True), x):
            return Not(x)
        case Xor(CValue(False), x):
            return x
        case Xor(x, y) if x == y:
            return CValue(False)
        case Xor(x, Not(y)) if x == y:
            return CValue(True)
        case Eq(BTerm() as x, BTerm() as y) if x == y:
            return CValue(True)
        case Eq(BTerm() as x, BNot(y)) if x == y:
            return CValue(False)
        case Eq(BValue(a), BNot(x)):
            mask = (1 << x.width) - 1
            return Eq(BValue(mask ^ a, x.width), x)
        case Eq(BValue(a), BAnd(BValue(b), x)) if a & (b ^ ((1 << x.width) - 1)) != 0:
            return CValue(False)
        case Eq(BValue(a), BOr(BValue(b), x)) if (a ^ ((1 << x.width) - 1)) & b != 0:
            return CValue(False)
        case Eq(BValue(a), BXor(BValue(b), x)):
            return Eq(BValue(a ^ b, x.width), x)
        case Eq(BValue(a), Add(BValue(b), x)):
            return Eq(Add(BValue(a, x.width), Neg(BValue(b, x.width))), x)
        case Ult(x, BValue(0)):
            return CValue(False)
        case Ult(BValue(0), x):
            return Distinct(x, BValue(0, x.width))
        case Ult(x, BValue(1)):
            return Eq(x, BValue(0, x.width))
        case Ule(x, BValue(0)):
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            return CValue(True)
        case Eq(BValue(a), ZeroExtend(_i, x)) if a >= (1 << x.width):
            return CValue(False)
        case Ult(ZeroExtend(_i, x), BValue(a)) if a >= (1 << x.width):
            return CValue(True)
        case Ult(BValue(a), ZeroExtend(_i, x)) if a >= (1 << x.width):
            return CValue(False)
        case Ule(ZeroExtend(_i, x), BValue(a)) if a >= (1 << x.width):
            return CValue(True)
        case Ule(BValue(a), ZeroExtend(_i, x)) if a >= (1 << x.width):
            return CValue(False)
        case term:
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
        case term:
            return term


def bitvector_folding(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
    match term:
        case Extract(i, j, BValue(a)):
            return BValue((a >> j) & ((1 << (i - j + 1)) - 1), i - j + 1)
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
            return BValue((a * b) % modulus, width)
        case Udiv(BValue(a), BValue(b)) if b != 0:
            return BValue(a // b, width)
        case Urem(BValue(a), BValue(b)) if b != 0:
            return BValue((a % b) % modulus, width)
        case Shl(BValue(a), BValue(b)):
            return BValue((a << b) % modulus, width)
        case Lshr(BValue(a), BValue(b)):
            return BValue((a >> b) % modulus, width)
        case Sdiv(BValue() as x, BValue(b) as y) if b != 0:
            return BValue(x.sgnd // y.sgnd, width)
        case Srem(BValue() as x, BValue(b) as y) if b != 0:
            r = abs(x.sgnd % y.sgnd)
            r = r if x.sgnd >= 0 else -r
            return BValue(r, width)
        case Smod(BValue() as x, BValue(b) as y) if b != 0:
            return BValue(x.sgnd % y.sgnd, width)
        case Ashr(BValue() as x, BValue(b)):
            return BValue(x.sgnd >> b, width)
        case ZeroExtend(_i, BValue(a)):
            return BValue(a, width)
        case SignExtend(_i, BValue() as x):
            return BValue(x.sgnd, width)
        case Ite(CValue(True), x, _y):
            return x
        case Ite(CValue(False), _x, y):
            return y
        case term:
            return term


def bitvector_logic(term: BTerm) -> BTerm:
    width = term.width
    mask = (1 << width) - 1
    modulus = 1 << width
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
        case BOr(BValue(0), x):
            return x
        case BOr(BValue(m), x) if m == mask:
            return BValue(mask, width)
        case BOr(x, y) if x == y:
            return x
        case BOr(x, BNot(y)) if x == y:
            return BValue(mask, width)
        case BXor(BValue(0), x):
            return x
        case BXor(BValue(m), x) if m == mask:
            return BNot(x)
        case BXor(x, y) if x == y:
            return BValue(0, width)
        case BXor(x, BNot(y)) if x == y:
            return BValue(mask, width)
        case BNot(Add(x, y)):
            return Add(BValue(1, width), Add(BNot(x), BNot(y)))
        case Add(BValue(0), x):
            return x
        case Add(x, BNot(y)) if x == y:
            return BValue(mask, width)
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
        case ZeroExtend(0, x):
            return x
        case ZeroExtend(i, ZeroExtend(j, x)):
            return ZeroExtend(i + j, x)
        case SignExtend(0, x):
            return x
        case SignExtend(i, SignExtend(j, x)):
            return SignExtend(i + j, x)
        case Ite(_c, x, y) if x == y:
            return x
        case BNot(Ite(c, x, y)):
            return Ite(c, BNot(x), BNot(y))
        case BAnd(Ite(c, x, y), z) | BAnd(z, Ite(c, x, y)):
            return Ite(c, BAnd(x, z), BAnd(y, z))
        case BOr(Ite(c, x, y), z) | BOr(z, Ite(c, x, y)):
            return Ite(c, BOr(x, z), BOr(y, z))
        case BXor(Ite(c, x, y), z) | BXor(z, Ite(c, x, y)):
            return Ite(c, BXor(x, z), BXor(y, z))
        case term:
            return term


def bitvector_yolo(term: BTerm) -> BTerm:
    match term:
        case Concat(terms) if all(isinstance(t, BValue) for t in terms):
            s = reduce(lambda p, q: (p << q.width) | cast(BValue, q).value, terms, 0)
            return BValue(s, term.width)
        case Concat([BValue(0) as z, *rest]):
            return ZeroExtend(z.width, Concat(tuple(rest)))
        case Concat([single]):
            return single
        case Shl(Concat([x, *rest]), BValue(a)) if a >= x.width:
            return Concat(
                (
                    Shl(Concat(tuple(rest)), BValue(a - x.width, term.width - x.width)),
                    BValue(0, x.width),
                )
            )
        case Lshr(Concat([*rest, x]), BValue(a)) if a >= x.width:
            return ZeroExtend(
                x.width,
                Lshr(Concat(tuple(rest)), BValue(a - x.width, term.width - x.width)),
            )
        case term:
            return term
