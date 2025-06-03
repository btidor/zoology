"""Higher-level SMT library incorporating rewrite rules."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field, fields
from typing import Any, ClassVar, override

from .theory_core import DumpContext, Symbolic


class RewriteMeta(abc.ABCMeta):
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        instance = super(RewriteMeta, self).__call__(*args, **kwds)
        match instance:
            case CompositeConstraint():
                return rewrite_constraint(instance)
            case CompositeBitVector():
                return rewrite_bitvector(instance)
            case _:
                raise NotImplementedError(instance)


@dataclass(frozen=True, slots=True)
class CompositeConstraint(Symbolic, metaclass=RewriteMeta): ...


@dataclass(frozen=True, slots=True)
class CoreSymbol(CompositeConstraint):
    name: bytes

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.out.extend(self.name)


@dataclass(frozen=True, slots=True)
class CoreValue(CompositeConstraint):
    CoreValue: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.out.extend(b"true" if self.CoreValue else b"false")


@dataclass(frozen=True, slots=True)
class CoreNot(CompositeConstraint):
    op: ClassVar[bytes] = b"CoreNot"
    term: CompositeConstraint


@dataclass(frozen=True, slots=True)
class CoreImplies(CompositeConstraint):
    op: ClassVar[bytes] = b"=>"
    left: CompositeConstraint
    right: CompositeConstraint


@dataclass(frozen=True, slots=True)
class CoreAnd(CompositeConstraint):
    op: ClassVar[bytes] = b"CoreAnd"
    left: CompositeConstraint
    right: CompositeConstraint


@dataclass(frozen=True, slots=True)
class CoreOr(CompositeConstraint):
    op: ClassVar[bytes] = b"CoreOr"
    left: CompositeConstraint
    right: CompositeConstraint


@dataclass(frozen=True, slots=True)
class CoreXor(CompositeConstraint):
    op: ClassVar[bytes] = b"CoreXor"
    left: CompositeConstraint
    right: CompositeConstraint


@dataclass(frozen=True, slots=True)
class CoreEq[S: Symbolic](CompositeConstraint):
    op: ClassVar[bytes] = b"="
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class CoreDistinct[S: Symbolic](CompositeConstraint):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class CoreIte(CompositeConstraint):
    op: ClassVar[bytes] = b"ite"
    cond: CompositeConstraint
    left: CompositeConstraint
    right: CompositeConstraint


def rewrite_constraint(term: CompositeConstraint) -> CompositeConstraint:
    match term:
        case CoreNot(CoreValue(val)):
            return CoreValue(not val)
        case CoreNot(CoreNot(inner)):
            return inner
        case CoreImplies(x, y):
            return CoreOr(y, CoreNot(x))
        case CoreAnd(CoreValue(True), x) | CoreAnd(x, CoreValue(True)):
            return x
        case CoreAnd(CoreValue(False), x) | CoreAnd(x, CoreValue(False)):
            return CoreValue(False)
        case CoreAnd(x, y) if x == y:
            return x
        case CoreAnd(x, CoreNot(y)) | CoreAnd(CoreNot(y), x) if x == y:
            return CoreValue(False)
        case CoreOr(CoreValue(True), x) | CoreOr(x, CoreValue(True)):
            return CoreValue(True)
        case CoreOr(CoreValue(False), x) | CoreOr(x, CoreValue(False)):
            return x
        case CoreOr(x, y) if x == y:
            return x
        case CoreOr(x, CoreNot(y)) | CoreOr(CoreNot(y), x) if x == y:
            return CoreValue(True)
        case CoreXor(CoreValue(True), x) | CoreXor(x, CoreValue(True)):
            return CoreNot(x)
        case CoreXor(CoreValue(False), x) | CoreXor(x, CoreValue(False)):
            return x
        case CoreXor(x, y) if x == y:
            return CoreValue(False)
        case CoreXor(x, CoreNot(y)) | CoreXor(CoreNot(y), x) if x == y:
            return CoreValue(True)
        case CoreEq(CompositeConstraint() as x, CompositeConstraint() as y):
            return CoreNot(CoreXor(x, y))
        case CoreDistinct(CompositeConstraint() as x, CompositeConstraint() as y):
            return CoreXor(x, y)
        case CoreIte(CoreValue(True), x, y):
            return x
        case CoreIte(CoreValue(False), x, y):
            return y
        case CoreIte(_, x, y) if x == y:
            return x
        # From rewrite_mixed:
        case CoreEq(BitVecValue(a), BitVecValue(b)):
            return CoreValue(a == b)
        case CoreEq(CompositeBitVector() as x, CompositeBitVector() as y) if x == y:
            return CoreValue(True)
        case CoreEq(CompositeBitVector() as x, BitVecNot(y)) | CoreEq(
            BitVecNot(y), CompositeBitVector() as x
        ) if x == y:
            return CoreValue(False)
        case CoreDistinct(CompositeBitVector() as x, CompositeBitVector() as y):
            return CoreNot(CoreEq(x, y))
        case CoreEq(BitVecValue(a), BitVecNot(x)) | CoreEq(
            BitVecNot(x), BitVecValue(a)
        ):
            mask = (1 << x.width) - 1
            return CoreEq(BitVecValue(mask ^ a, x.width), x)
        case (
            CoreEq(BitVecValue(a), BitVecAnd(x, BitVecValue(b)))
            | CoreEq(BitVecValue(a), BitVecAnd(BitVecValue(b), x))
            | CoreEq(BitVecAnd(x, BitVecValue(b)), BitVecValue(a))
            | CoreEq(BitVecAnd(BitVecValue(b), x), BitVecValue(a))
        ) if a & (b ^ ((1 << x.width) - 1)) != 0:
            return CoreValue(False)
        case (
            CoreEq(BitVecValue(a), BitVecOr(x, BitVecValue(b)))
            | CoreEq(BitVecValue(a), BitVecOr(BitVecValue(b), x))
            | CoreEq(BitVecOr(x, BitVecValue(b)), BitVecValue(a))
            | CoreEq(BitVecOr(BitVecValue(b), x), BitVecValue(a))
        ) if (a ^ (1 << x.width) - 1) & b != 0:
            return CoreValue(False)
        case (
            CoreEq(BitVecValue(a), BitVecXor(x, BitVecValue(b)))
            | CoreEq(BitVecValue(a), BitVecXor(BitVecValue(b), x))
            | CoreEq(BitVecXor(x, BitVecValue(b)), BitVecValue(a))
            | CoreEq(BitVecXor(BitVecValue(b), x), BitVecValue(a))
        ):
            return CoreEq(BitVecValue(a ^ b, x.width), x)
        case (
            CoreEq(BitVecValue(a), BitVecAdd(x, BitVecValue(b)))
            | CoreEq(BitVecValue(a), BitVecAdd(BitVecValue(b), x))
            | CoreEq(BitVecAdd(x, BitVecValue(b)), BitVecValue(a))
            | CoreEq(BitVecAdd(BitVecValue(b), x), BitVecValue(a))
        ):
            return CoreEq(
                BitVecAdd(BitVecValue(a, x.width), BitVecNeg(BitVecValue(b, x.width))),
                x,
            )
        case BitVecUlt(BitVecValue(a), BitVecValue(b)):
            return CoreValue(a < b)
        case BitVecUlt(x, BitVecValue(0)):
            return CoreValue(False)
        case BitVecUlt(BitVecValue(0), x):
            return CoreDistinct(x, BitVecValue(0, x.width))
        case BitVecUlt(x, BitVecValue(1)):
            return CoreEq(x, BitVecValue(0, x.width))
        case BitVecUle(BitVecValue(a), BitVecValue(b)):
            return CoreValue(a <= b)
        case BitVecUle(x, BitVecValue(0)):
            return CoreEq(x, BitVecValue(0, x.width))
        case BitVecUle(BitVecValue(0), x):
            return CoreValue(True)
        case BitVecUgt(x, y):
            return BitVecUlt(y, x)
        case BitVecUge(x, y):
            return BitVecUle(y, x)
        case BitVecSgt(x, y):
            return BitVecSlt(y, x)
        case BitVecSge(x, y):
            return BitVecSle(y, x)
        case term:
            return term


@dataclass(frozen=True, slots=True)
class CompositeBitVector(Symbolic, metaclass=RewriteMeta):
    width: int = field(init=False)

    def __post_init__(self) -> None:
        # By default, inherit width from inner term.
        for field in fields(self):
            if field.type == "CompositeBitVector":
                term = getattr(self, field.name)
                object.__setattr__(self, "width", term.width)
                break
        else:
            raise TypeError(f"could not find inner term for {self.__class__.__name__}")


@dataclass(frozen=True, slots=True)
class BitVecSymbol(CompositeBitVector):
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
class BitVecValue(CompositeBitVector):
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
class UnaryOp(CompositeBitVector):
    term: CompositeBitVector


@dataclass(frozen=True, slots=True)
class BinaryOp(CompositeBitVector):
    left: CompositeBitVector
    right: CompositeBitVector


@dataclass(frozen=True, slots=True)
class CompareOp(CompositeConstraint):
    left: CompositeBitVector
    right: CompositeBitVector


@dataclass(frozen=True, slots=True)
class SingleParamOp(CompositeBitVector):
    i: int
    term: CompositeBitVector


@dataclass(frozen=True, slots=True)
class BitVecConcat(CompositeBitVector):
    op: ClassVar[bytes] = b"concat"
    left: CompositeBitVector
    right: CompositeBitVector

    @override
    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.left.width + self.right.width)


@dataclass(frozen=True, slots=True)
class BitVecExtract(CompositeBitVector):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: CompositeBitVector

    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        w = self.i - self.j + 1
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class BitVecNot(UnaryOp):
    op: ClassVar[bytes] = b"bvnot"


@dataclass(frozen=True, slots=True)
class BitVecAnd(BinaryOp):
    op: ClassVar[bytes] = b"bvand"


@dataclass(frozen=True, slots=True)
class BitVecOr(CompositeBitVector):
    op: ClassVar[bytes] = b"bvor"
    left: CompositeBitVector
    right: CompositeBitVector


@dataclass(frozen=True, slots=True)
class BitVecNeg(UnaryOp):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(frozen=True, slots=True)
class BitVecAdd(BinaryOp):
    op: ClassVar[bytes] = b"bvadd"


@dataclass(frozen=True, slots=True)
class BitVecMul(BinaryOp):
    op: ClassVar[bytes] = b"bvmul"


@dataclass(frozen=True, slots=True)
class BitVecUdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvudiv"


@dataclass(frozen=True, slots=True)
class BitVecUrem(BinaryOp):
    op: ClassVar[bytes] = b"bvurem"


@dataclass(frozen=True, slots=True)
class BitVecShl(BinaryOp):
    op: ClassVar[bytes] = b"bvshl"


@dataclass(frozen=True, slots=True)
class BitVecLshr(BinaryOp):
    op: ClassVar[bytes] = b"bvlshr"


@dataclass(frozen=True, slots=True)
class BitVecUlt(CompareOp):
    op: ClassVar[bytes] = b"bvult"


@dataclass(frozen=True, slots=True)
class BitVecNand(BinaryOp):
    op: ClassVar[bytes] = b"bvnand"


@dataclass(frozen=True, slots=True)
class BitVecNor(BinaryOp):
    op: ClassVar[bytes] = b"bvnor"


@dataclass(frozen=True, slots=True)
class BitVecXor(BinaryOp):
    op: ClassVar[bytes] = b"bvxor"


@dataclass(frozen=True, slots=True)
class BitVecXnor(BinaryOp):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(frozen=True, slots=True)
class BitVecComp(CompositeBitVector):  # width-1 result
    op: ClassVar[bytes] = b"bvcomp"
    left: CompositeBitVector
    right: CompositeBitVector


@dataclass(frozen=True, slots=True)
class BitVecSub(BinaryOp):
    op: ClassVar[bytes] = b"bvsub"


@dataclass(frozen=True, slots=True)
class BitVecSdiv(BinaryOp):
    op: ClassVar[bytes] = b"bvsdiv"


@dataclass(frozen=True, slots=True)
class BitVecSrem(BinaryOp):
    op: ClassVar[bytes] = b"bvsrem"


@dataclass(frozen=True, slots=True)
class BitVecSmod(BinaryOp):
    op: ClassVar[bytes] = b"bvsmod"


@dataclass(frozen=True, slots=True)
class BitVecAshr(BinaryOp):
    op: ClassVar[bytes] = b"bvashr"


@dataclass(frozen=True, slots=True)
class BitVecRepeat(SingleParamOp):
    op: ClassVar[bytes] = b"repeat"

    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class BitVecZeroExtend(SingleParamOp):
    op: ClassVar[bytes] = b"zero_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class BitVecSignExtend(SingleParamOp):
    op: ClassVar[bytes] = b"sign_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class BitVecRotateLeft(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_left"


@dataclass(frozen=True, slots=True)
class BitVecRotateRight(SingleParamOp):
    op: ClassVar[bytes] = b"rotate_right"


@dataclass(frozen=True, slots=True)
class BitVecUle(CompareOp):
    op: ClassVar[bytes] = b"bvule"


@dataclass(frozen=True, slots=True)
class BitVecUgt(CompareOp):
    op: ClassVar[bytes] = b"bvugt"


@dataclass(frozen=True, slots=True)
class BitVecUge(CompareOp):
    op: ClassVar[bytes] = b"bvuge"


@dataclass(frozen=True, slots=True)
class BitVecSlt(CompareOp):
    op: ClassVar[bytes] = b"bvslt"


@dataclass(frozen=True, slots=True)
class BitVecSle(CompareOp):
    op: ClassVar[bytes] = b"bvsle"


@dataclass(frozen=True, slots=True)
class BitVecSgt(CompareOp):
    op: ClassVar[bytes] = b"bvsgt"


@dataclass(frozen=True, slots=True)
class BitVecSge(CompareOp):
    op: ClassVar[bytes] = b"bvsge"


@dataclass(frozen=True, slots=True)
class BitVecIte(CompositeBitVector):
    op: ClassVar[bytes] = b"ite"
    cond: CompositeConstraint
    left: CompositeBitVector
    right: CompositeBitVector


def rewrite_bitvector(term: CompositeBitVector) -> CompositeBitVector:
    width = term.width
    mask = (1 << term.width) - 1
    modulus = 1 << term.width
    match term:
        case BitVecNot(BitVecValue(val)):
            return BitVecValue(mask ^ val, width)
        case BitVecNot(BitVecNot(inner)):
            return inner
        case BitVecAnd(BitVecValue(a), BitVecValue(b)):
            return BitVecValue(a & b, width)
        case BitVecAnd(BitVecValue(0), x) | BitVecAnd(x, BitVecValue(0)):
            return BitVecValue(0, width)
        case BitVecAnd(BitVecValue(m), x) | BitVecAnd(x, BitVecValue(m)) if m == mask:
            return x
        case BitVecAnd(x, y) if x == y:
            return x
        case BitVecAnd(x, BitVecNot(y)) | BitVecAnd(BitVecNot(y), x) if x == y:
            return BitVecValue(0, width)
        case BitVecOr(BitVecValue(a), BitVecValue(b)):
            return BitVecValue(a | b, width)
        case BitVecOr(BitVecValue(0), x) | BitVecOr(x, BitVecValue(0)):
            return x
        case BitVecOr(BitVecValue(m), x) | BitVecOr(x, BitVecValue(m)) if m == mask:
            return BitVecValue(mask, width)
        case BitVecOr(x, y) if x == y:
            return x
        case BitVecOr(x, BitVecNot(y)) | BitVecOr(BitVecNot(y), x) if x == y:
            return BitVecValue(mask, width)
        case BitVecXor(BitVecValue(a), BitVecValue(b)):
            return BitVecValue(a ^ b, width)
        case BitVecXor(BitVecValue(0), x) | BitVecXor(x, BitVecValue(0)):
            return x
        case BitVecXor(BitVecValue(m), x) | BitVecXor(x, BitVecValue(m)) if m == mask:
            return BitVecNot(x)
        case BitVecXor(x, y) if x == y:
            return BitVecValue(0, width)
        case BitVecXor(x, BitVecNot(y)) | BitVecXor(BitVecNot(y), x) if x == y:
            return BitVecValue(mask, width)
        case BitVecNand(x, y):
            return BitVecNot(BitVecAnd(x, y))
        case BitVecNor(x, y):
            return BitVecNot(BitVecOr(x, y))
        case BitVecXnor(x, y):
            return BitVecNot(BitVecXor(x, y))
        case BitVecAdd(BitVecValue(a), BitVecValue(b)):
            return BitVecValue((a + b) % modulus, width)
        case BitVecAdd(BitVecValue(0), x) | BitVecAdd(x, BitVecValue(0)):
            return x
        case BitVecMul(BitVecValue(a), BitVecValue(b)):
            return BitVecValue((a * b) % modulus, width)
        case BitVecMul(BitVecValue(0), x) | BitVecMul(x, BitVecValue(0)):
            return BitVecValue(0, width)
        case BitVecMul(BitVecValue(1), x) | BitVecMul(x, BitVecValue(1)):
            return x
        case BitVecUdiv(BitVecValue(a), BitVecValue(b)) if b != 0:
            return BitVecValue(a // b, width)
        case BitVecUdiv(x, BitVecValue(0)):
            return BitVecValue(mask, width)
        case BitVecUdiv(x, BitVecValue(1)):
            return x
        case BitVecUrem(BitVecValue(a), BitVecValue(b)) if b != 0:
            return BitVecValue((a % b) % modulus, width)
        case BitVecUrem(x, BitVecValue(0)):
            return x
        case BitVecNeg(x):
            return BitVecAdd(BitVecNot(x), BitVecValue(1, width))
        case BitVecSub(x, y):
            return BitVecAdd(BitVecAdd(x, BitVecNot(y)), BitVecValue(1, width))
        case BitVecNot(BitVecAdd(x, y)):
            return BitVecAdd(
                BitVecAdd(BitVecNot(x), BitVecNot(y)), BitVecValue(1, width)
            )
        case BitVecShl(BitVecValue(a), BitVecValue(b)):
            return BitVecValue((a << b) % modulus, width)
        case BitVecShl(x, BitVecValue(val)) if val >= width:
            return BitVecValue(0, width)
        case BitVecShl(BitVecShl(x, BitVecValue(a)), BitVecValue(b)) if (
            a < width and b < width
        ):
            return BitVecShl(x, BitVecValue(a + b, width))
        case BitVecLshr(BitVecValue(a), BitVecValue(b)):
            return BitVecValue((a >> b) % modulus, width)
        case BitVecLshr(x, BitVecValue(val)) if val >= width:
            return BitVecValue(0, width)
        case BitVecLshr(BitVecLshr(x, BitVecValue(a)), BitVecValue(b)) if (
            a < width and b < width
        ):
            return BitVecLshr(x, BitVecValue(a + b, width))
        case BitVecZeroExtend(0, x):
            return x
        case BitVecSignExtend(0, x):
            return x
        case BitVecConcat(BitVecValue(a) as x, BitVecValue(b) as y):
            return BitVecValue((a << y.width) | b, x.width + y.width)
        case BitVecIte(CoreValue(True), x, y):
            return x
        case BitVecIte(CoreValue(False), x, y):
            return y
        case BitVecIte(_, x, y) if x == y:
            return x
        case BitVecNot(BitVecIte(c, x, y)):
            return BitVecIte(c, BitVecNot(x), BitVecNot(y))
        case BitVecAnd(BitVecIte(c, x, y), z) | BitVecAnd(z, BitVecIte(c, x, y)):
            return BitVecIte(c, BitVecAnd(x, z), BitVecAnd(y, z))
        case BitVecOr(BitVecIte(c, x, y), z) | BitVecOr(z, BitVecIte(c, x, y)):
            return BitVecIte(c, BitVecOr(x, z), BitVecOr(y, z))
        case BitVecXor(BitVecIte(c, x, y), z) | BitVecXor(z, BitVecIte(c, x, y)):
            return BitVecIte(c, BitVecXor(x, z), BitVecXor(y, z))
        case term:
            return term


@dataclass(frozen=True, slots=True)
class CompositeArray(Symbolic):
    @abc.abstractmethod
    def value_width(self) -> int: ...


@dataclass(frozen=True, slots=True)
class ArraySymbol(CompositeArray):
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
class ArrayValue(CompositeArray):
    default: CompositeBitVector
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
class ArraySelect(CompositeBitVector):
    op: ClassVar[bytes] = b"select"
    array: CompositeArray
    key: CompositeBitVector

    @override
    def __post_init__(self) -> None:
        object.__setattr__(self, "width", self.array.value_width())


@dataclass(frozen=True, slots=True)
class ArrayStore(CompositeArray):
    default: ArraySymbol | ArrayValue
    lower: frozenset[tuple[int, CompositeBitVector]] = frozenset()
    upper: tuple[tuple[CompositeBitVector, CompositeBitVector], ...] = ()

    def value_width(self) -> int:
        return self.default.value_width()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[CompositeBitVector, CompositeBitVector]](
            [(BitVecValue(k, self.default.key), v) for k, v in self.lower]
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
