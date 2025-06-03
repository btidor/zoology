"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analysis

"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field, fields
from typing import Any, ClassVar, override

from .theory_core import Base, DumpContext


class RewriteMeta(abc.ABCMeta):
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        instance = super(RewriteMeta, self).__call__(*args, **kwds)
        match instance:
            case Constraint():
                return rewrite_constraint(instance)
            case BitVector():
                return rewrite_bitvector(instance)
            case _:
                raise NotImplementedError(instance)


@dataclass(frozen=True, slots=True)
class Constraint(Base, metaclass=RewriteMeta): ...


@dataclass(frozen=True, slots=True)
class CSymbol(Constraint):
    name: bytes

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.out.extend(self.name)


@dataclass(frozen=True, slots=True)
class CValue(Constraint):
    value: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.out.extend(b"true" if self.value else b"false")


@dataclass(frozen=True, slots=True)
class Not(Constraint):
    op: ClassVar[bytes] = b"not"
    term: Constraint


@dataclass(frozen=True, slots=True)
class Implies(Constraint):
    op: ClassVar[bytes] = b"=>"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class And(Constraint):
    op: ClassVar[bytes] = b"and"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Or(Constraint):
    op: ClassVar[bytes] = b"or"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Xor(Constraint):
    op: ClassVar[bytes] = b"xor"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Eq[S: Base](Constraint):
    op: ClassVar[bytes] = b"="
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class Distinct[S: Base](Constraint):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class CIte(Constraint):
    op: ClassVar[bytes] = b"ite"
    cond: Constraint
    left: Constraint
    right: Constraint


def rewrite_constraint(term: Constraint) -> Constraint:
    match term:
        case Not(CValue(val)):
            return CValue(not val)
        case Not(Not(inner)):
            return inner
        case Implies(x, y):
            return Or(y, Not(x))
        case And(CValue(True), x) | And(x, CValue(True)):
            return x
        case And(CValue(False), x) | And(x, CValue(False)):
            return CValue(False)
        case And(x, y) if x == y:
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:
            return CValue(False)
        case Or(CValue(True), x) | Or(x, CValue(True)):
            return CValue(True)
        case Or(CValue(False), x) | Or(x, CValue(False)):
            return x
        case Or(x, y) if x == y:
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:
            return CValue(True)
        case Xor(CValue(True), x) | Xor(x, CValue(True)):
            return Not(x)
        case Xor(CValue(False), x) | Xor(x, CValue(False)):
            return x
        case Xor(x, y) if x == y:
            return CValue(False)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:
            return CValue(True)

        case Eq(Constraint() as x, Constraint() as y):
            return Not(Xor(x, y))
        case Eq(BitVector() as x, BitVector() as y) if x == y:
            return CValue(True)
        case Eq(BitVector() as x, BNot(y)) | Eq(BNot(y), BitVector() as x) if x == y:
            return CValue(False)
        case Distinct(Constraint() as x, Constraint() as y):
            return Xor(x, y)
        case Distinct(BitVector() as x, BitVector() as y):
            return Not(Eq(x, y))
        case CIte(CValue(True), x, y):
            return x
        case CIte(CValue(False), x, y):
            return y
        case CIte(_, x, y) if x == y:
            return x
        case Eq(BValue(a), BNot(x)) | Eq(BNot(x), BValue(a)):
            mask = (1 << x.width) - 1
            return Eq(BValue(mask ^ a, x.width), x)
        case (
            Eq(BValue(a), BAnd(x, BValue(b)))
            | Eq(BValue(a), BAnd(BValue(b), x))
            | Eq(BAnd(x, BValue(b)), BValue(a))
            | Eq(BAnd(BValue(b), x), BValue(a))
        ) if a & (b ^ ((1 << x.width) - 1)) != 0:
            return CValue(False)
        case (
            Eq(BValue(a), BOr(x, BValue(b)))
            | Eq(BValue(a), BOr(BValue(b), x))
            | Eq(BOr(x, BValue(b)), BValue(a))
            | Eq(BOr(BValue(b), x), BValue(a))
        ) if (a ^ (1 << x.width) - 1) & b != 0:
            return CValue(False)
        case (
            Eq(BValue(a), BXor(x, BValue(b)))
            | Eq(BValue(a), BXor(BValue(b), x))
            | Eq(BXor(x, BValue(b)), BValue(a))
            | Eq(BXor(BValue(b), x), BValue(a))
        ):
            return Eq(BValue(a ^ b, x.width), x)
        case (
            Eq(BValue(a), Add(x, BValue(b)))
            | Eq(BValue(a), Add(BValue(b), x))
            | Eq(Add(x, BValue(b)), BValue(a))
            | Eq(Add(BValue(b), x), BValue(a))
        ):
            return Eq(Add(BValue(a, x.width), Neg(BValue(b, x.width))), x)
        case Ult(BValue(a), BValue(b)):
            return CValue(a < b)
        case Ult(x, BValue(0)):
            return CValue(False)
        case Ult(BValue(0), x):
            return Distinct(x, BValue(0, x.width))
        case Ult(x, BValue(1)):
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(a), BValue(b)):
            return CValue(a <= b)
        case Ule(x, BValue(0)):
            return Eq(x, BValue(0, x.width))
        case Ule(BValue(0), x):
            return CValue(True)
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


@dataclass(frozen=True, slots=True)
class BitVector(Base, metaclass=RewriteMeta):
    width: int = field(init=False)

    def __post_init__(self) -> None:
        for fld in fields(self):
            if fld.type == "BitVector":
                term = getattr(self, fld.name)
                object.__setattr__(self, "width", term.width)
                break
        else:
            raise TypeError(f"could not find inner term for {self.__class__.__name__}")


@dataclass(frozen=True, slots=True)
class BSymbol(BitVector):
    name: bytes
    w: InitVar[int]

    @override
    def __post_init__(self, w: int) -> None:
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (b"(declare-fun %s () (_ BitVec %d))" % (self.name, self.width)),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class BValue(BitVector):
    value: int
    w: InitVar[int]

    @override
    def __post_init__(self, w: int) -> None:
        assert 0 <= self.value < (1 << w)
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())


@dataclass(frozen=True, slots=True)
class UnaryOp(BitVector):
    term: BitVector


@dataclass(frozen=True, slots=True)
class BinaryOp(BitVector):
    left: BitVector
    right: BitVector


@dataclass(frozen=True, slots=True)
class CompareOp(Constraint):
    left: BitVector
    right: BitVector


@dataclass(frozen=True, slots=True)
class SingleParamOp(BitVector):
    i: int
    term: BitVector


@dataclass(frozen=True, slots=True)
class Concat(BitVector):
    op: ClassVar[bytes] = b"concat"
    left: BitVector
    right: BitVector

    @override
    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.left.width + self.right.width)


@dataclass(frozen=True, slots=True)
class Extract(BitVector):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BitVector

    @override
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


@dataclass(frozen=True, slots=True)
class BOr(BitVector):
    op: ClassVar[bytes] = b"bvor"
    left: BitVector
    right: BitVector


@dataclass(frozen=True, slots=True)
class Neg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(frozen=True, slots=True)
class Add(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"


@dataclass(frozen=True, slots=True)
class Mul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"


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


@dataclass(frozen=True, slots=True)
class Xnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(frozen=True, slots=True)
class Comp(BitVector):
    op: ClassVar[bytes] = b"bvcomp"
    left: BitVector
    right: BitVector


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

    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class ZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class SignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class RotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"


@dataclass(frozen=True, slots=True)
class RotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"


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
class Ite(BitVector):
    op: ClassVar[bytes] = b"ite"
    cond: Constraint
    left: BitVector
    right: BitVector


def rewrite_bitvector(term: BitVector) -> BitVector:
    width = term.width
    mask = (1 << term.width) - 1
    modulus = 1 << term.width
    match term:
        case BNot(BValue(val)):
            return BValue(mask ^ val, width)
        case BNot(BNot(inner)):
            return inner
        case BAnd(BValue(a), BValue(b)):
            return BValue(a & b, width)
        case BAnd(BValue(0), x) | BAnd(x, BValue(0)):
            return BValue(0, width)
        case BAnd(BValue(m), x) | BAnd(x, BValue(m)) if m == mask:
            return x
        case BAnd(x, y) if x == y:
            return x
        case BAnd(x, BNot(y)) | BAnd(BNot(y), x) if x == y:
            return BValue(0, width)
        case BOr(BValue(a), BValue(b)):
            return BValue(a | b, width)
        case BOr(BValue(0), x) | BOr(x, BValue(0)):
            return x
        case BOr(BValue(m), x) | BOr(x, BValue(m)) if m == mask:
            return BValue(mask, width)
        case BOr(x, y) if x == y:
            return x
        case BOr(x, BNot(y)) | BOr(BNot(y), x) if x == y:
            return BValue(mask, width)
        case BXor(BValue(a), BValue(b)):
            return BValue(a ^ b, width)
        case BXor(BValue(0), x) | BXor(x, BValue(0)):
            return x
        case BXor(BValue(m), x) | BXor(x, BValue(m)) if m == mask:
            return BNot(x)
        case BXor(x, y) if x == y:
            return BValue(0, width)
        case BXor(x, BNot(y)) | BXor(BNot(y), x) if x == y:
            return BValue(mask, width)
        case Nand(x, y):
            return BNot(BAnd(x, y))
        case Nor(x, y):
            return BNot(BOr(x, y))
        case Xnor(x, y):
            return BNot(BXor(x, y))
        case Add(BValue(a), BValue(b)):
            return BValue((a + b) % modulus, width)
        case Add(BValue(0), x) | Add(x, BValue(0)):
            return x
        case Mul(BValue(a), BValue(b)):
            return BValue((a * b) % modulus, width)
        case Mul(BValue(0), x) | Mul(x, BValue(0)):
            return BValue(0, width)
        case Mul(BValue(1), x) | Mul(x, BValue(1)):
            return x
        case Udiv(BValue(a), BValue(b)) if b != 0:
            return BValue(a // b, width)
        case Udiv(x, BValue(0)):
            return BValue(mask, width)
        case Udiv(x, BValue(1)):
            return x
        case Urem(BValue(a), BValue(b)) if b != 0:
            return BValue((a % b) % modulus, width)
        case Urem(x, BValue(0)):
            return x
        case Neg(x):
            return Add(BNot(x), BValue(1, width))
        case Sub(x, y):
            return Add(Add(x, BNot(y)), BValue(1, width))
        case BNot(Add(x, y)):
            return Add(Add(BNot(x), BNot(y)), BValue(1, width))
        case Shl(BValue(a), BValue(b)):
            return BValue((a << b) % modulus, width)
        case Shl(x, BValue(val)) if val >= width:
            return BValue(0, width)
        case Shl(Shl(x, BValue(a)), BValue(b)) if a < width and b < width:
            return Shl(x, BValue(a + b, width))
        case Lshr(BValue(a), BValue(b)):
            return BValue((a >> b) % modulus, width)
        case Lshr(x, BValue(val)) if val >= width:
            return BValue(0, width)
        case Lshr(Lshr(x, BValue(a)), BValue(b)) if a < width and b < width:
            return Lshr(x, BValue(a + b, width))
        case ZeroExtend(0, x):
            return x
        case SignExtend(0, x):
            return x
        case Concat(BValue(a) as x, BValue(b) as y):
            return BValue((a << y.width) | b, x.width + y.width)
        case Ite(CValue(True), x, y):
            return x
        case Ite(CValue(False), x, y):
            return y
        case Ite(_, x, y) if x == y:
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


@dataclass(frozen=True, slots=True)
class Array(Base):
    @abc.abstractmethod
    def value_width(self) -> int: ...


@dataclass(frozen=True, slots=True)
class ASymbol(Array):
    name: bytes
    key: int
    value: int

    def value_width(self) -> int:
        return self.value

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
class AValue(Array):
    default: BitVector
    key: int

    def value_width(self) -> int:
        return self.default.width

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((_ as const (Array (_ BitVec %d) (_ BitVec %d)))"
            % (self.key, self.default.width)
        )
        self.default.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Select(BitVector):
    op: ClassVar[bytes] = b"select"
    array: Array
    key: BitVector

    @override
    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.array.value_width())


@dataclass(frozen=True, slots=True)
class Store(Array):
    default: ASymbol | AValue
    lower: frozenset[tuple[int, BitVector]] = frozenset()
    upper: tuple[tuple[BitVector, BitVector], ...] = ()

    def value_width(self) -> int:
        return self.default.value_width()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[BitVector, BitVector]](
            [(BValue(k, self.default.key), v) for k, v in self.lower]
        )
        writes.extend(self.upper)
        ctx.write(b"(store " * len(writes))
        self.default.dump(ctx)
        for k, v in writes:
            ctx.write(b" ")
            k.dump(ctx)
            ctx.write(b" ")
            v.dump(ctx)
            ctx.write(b")")
