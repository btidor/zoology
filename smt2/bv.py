"""
Definitions for the theory of bitvectors.

Up-to-date with SMT-LIB version 2.7, QF_BV logic.

See: https://smt-lib.org/logics-all.shtml#QF_BV
"""
# ruff: noqa

from __future__ import annotations

from dataclasses import InitVar, dataclass, field, fields
from functools import reduce
from typing import ClassVar, Literal, override

from .core import Constraint, DumpContext, Symbolic


@dataclass(frozen=True, slots=True)
class BitVector[N: int](Symbolic):
    width: N = field(init=False)

    def __post_init__(self) -> None:
        # By default, inherit width from inner term.
        for field in fields(self):
            if field.type == "BitVector[N]":
                term = getattr(self, field.name)
                object.__setattr__(self, "width", term.width)
                break
        else:
            raise TypeError(f"could not find inner term for {self.__class__.__name__}")


@dataclass(frozen=True, slots=True)
class Symbol[N: int](BitVector[N]):
    name: bytes
    w: InitVar[N]

    @override
    def __post_init__(self, w: N) -> None:
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (b"(declare-fun %s () (_ BitVec %d))" % (self.name, self.width)),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class Value[N: int](BitVector[N]):
    value: int
    w: InitVar[N]

    @override
    def __post_init__(self, w: N) -> None:
        assert 0 <= self.value < (1 << w)
        object.__setattr__(self, "width", w)

    @override
    def dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self.value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self.value)[2:].zfill(self.width).encode())


@dataclass(frozen=True, slots=True)
class UnaryOp[N: int](BitVector[N]):
    term: BitVector[N]


@dataclass(frozen=True, slots=True)
class BinaryOp[N: int](BitVector[N]):
    left: BitVector[N]
    right: BitVector[N]


@dataclass(frozen=True, slots=True)
class CompareOp[N: int](Constraint):
    left: BitVector[N]
    right: BitVector[N]


@dataclass(frozen=True, slots=True)
class SingleParamOp[N: int](BitVector[N]):
    i: int
    term: BitVector[int]


@dataclass(frozen=True, slots=True)
class Concat[N: int](BitVector[N]):
    terms: tuple[BitVector[int], ...]

    @override
    def __post_init__(self) -> None:
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
class Extract[N: int](BitVector[N]):
    op: ClassVar[bytes] = b"extract"
    i: int
    j: int
    term: BitVector[int]

    @override
    def __post_init__(self) -> None:
        assert self.term.width > self.i >= self.j >= 0
        w = self.i - self.j + 1
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class Not[N: int](UnaryOp[N]):
    op: ClassVar[bytes] = b"bvnot"


@dataclass(frozen=True, slots=True)
class And[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvand"


@dataclass(frozen=True, slots=True)
class Or[N: int](BitVector[N]):
    op: ClassVar[bytes] = b"bvor"
    left: BitVector[N]
    right: BitVector[N]


@dataclass(frozen=True, slots=True)
class Neg[N: int](UnaryOp[N]):
    op: ClassVar[bytes] = b"bvneg"


@dataclass(frozen=True, slots=True)
class Add[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvadd"


@dataclass(frozen=True, slots=True)
class Mul[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvmul"


@dataclass(frozen=True, slots=True)
class Udiv[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvudiv"


@dataclass(frozen=True, slots=True)
class Urem[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvurem"


@dataclass(frozen=True, slots=True)
class Shl[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvshl"


@dataclass(frozen=True, slots=True)
class Lshr[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvlshr"


@dataclass(frozen=True, slots=True)
class Ult[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvult"


@dataclass(frozen=True, slots=True)
class Nand[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvnand"


@dataclass(frozen=True, slots=True)
class Nor[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvnor"


@dataclass(frozen=True, slots=True)
class Xor[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvxor"


@dataclass(frozen=True, slots=True)
class Xnor[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvxnor"


@dataclass(frozen=True, slots=True)
class Comp[N: int](BitVector[Literal[1]]):
    op: ClassVar[bytes] = b"bvcomp"
    left: BitVector[N]
    right: BitVector[N]


@dataclass(frozen=True, slots=True)
class Sub[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvsub"


@dataclass(frozen=True, slots=True)
class Sdiv[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvsdiv"


@dataclass(frozen=True, slots=True)
class Srem[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvsrem"


@dataclass(frozen=True, slots=True)
class Smod[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvsmod"


@dataclass(frozen=True, slots=True)
class Ashr[N: int](BinaryOp[N]):
    op: ClassVar[bytes] = b"bvashr"


@dataclass(frozen=True, slots=True)
class Repeat[N: int](SingleParamOp[N]):
    op: ClassVar[bytes] = b"repeat"

    @override
    def __post_init__(self) -> None:
        assert self.i > 0
        w = self.term.width * self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class ZeroExtend[N: int](SingleParamOp[N]):
    op: ClassVar[bytes] = b"zero_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class SignExtend[N: int](SingleParamOp[N]):
    op: ClassVar[bytes] = b"sign_extend"

    @override
    def __post_init__(self) -> None:
        assert self.i >= 0
        w = self.term.width + self.i
        object.__setattr__(self, "width", w)


@dataclass(frozen=True, slots=True)
class RotateLeft[N: int](SingleParamOp[N]):
    op: ClassVar[bytes] = b"rotate_left"


@dataclass(frozen=True, slots=True)
class RotateRight[N: int](SingleParamOp[N]):
    op: ClassVar[bytes] = b"rotate_right"


@dataclass(frozen=True, slots=True)
class Ule[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvule"


@dataclass(frozen=True, slots=True)
class Ugt[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvugt"


@dataclass(frozen=True, slots=True)
class Uge[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvuge"


@dataclass(frozen=True, slots=True)
class Slt[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvslt"


@dataclass(frozen=True, slots=True)
class Sle[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvsle"


@dataclass(frozen=True, slots=True)
class Sgt[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvsgt"


@dataclass(frozen=True, slots=True)
class Sge[N: int](CompareOp[N]):
    op: ClassVar[bytes] = b"bvsge"


@dataclass(frozen=True, slots=True)
class Ite[N: int](BitVector[N]):
    op: ClassVar[bytes] = b"ite"
    cond: Constraint
    left: BitVector[N]
    right: BitVector[N]
