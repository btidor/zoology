"""
Definitions for the theory of arrays.

Up-to-date with SMT-LIB version 2.7, QF_ABV logic.

See: https://smt-lib.org/theories-ArraysEx.shtml
"""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass
from typing import ClassVar, override

from .theory_core import DumpContext, Symbolic
from .theory_bitvec import BitVector
from . import theory_bitvec as bv


@dataclass(frozen=True, slots=True)
class Array(Symbolic):
    @abc.abstractmethod
    def value_width(self) -> int: ...


@dataclass(frozen=True, slots=True)
class Symbol(Array):
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
class Value(Array):
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
    default: Symbol | Value
    lower: frozenset[tuple[int, BitVector]] = frozenset()
    upper: tuple[tuple[BitVector, BitVector], ...] = ()

    def value_width(self) -> int:
        return self.default.value_width()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[BitVector, BitVector]](
            [(bv.Value(k, self.default.key), v) for k, v in self.lower]
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
