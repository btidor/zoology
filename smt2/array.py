"""
Definitions for the theory of arrays.

Up-to-date with SMT-LIB version 2.7, QF_ABV logic.

See: https://smt-lib.org/theories-ArraysEx.shtml
"""
# ruff: noqa

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar, override

from .core import DumpContext, Symbolic
from .bv import BitVector
from . import bv


@dataclass(frozen=True, slots=True)
class Array[K: int, V: int](Symbolic): ...


@dataclass(frozen=True, slots=True)
class Symbol[K: int, V: int](Array[K, V]):
    name: bytes
    key: K
    value: V

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
class Value[K: int, V: int](Array[K, V]):
    default: BitVector[V]
    key: K
    value: V

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((_ as const (Array (_ BitVec %d) (_ BitVec %d)))"
            % (self.key, self.value)
        )
        self.default.dump(ctx)
        ctx.write(b")")


@dataclass(frozen=True, slots=True)
class Select[K: int, V: int](BitVector[V]):
    op: ClassVar[bytes] = b"select"
    array: Array[K, V]
    key: BitVector[K]


@dataclass(frozen=True, slots=True)
class Store[K: int, V: int](Array[K, V]):
    default: Symbol[K, V] | Value[K, V]
    lower: frozenset[tuple[int, BitVector[V]]] = frozenset()
    upper: tuple[tuple[BitVector[K], BitVector[V]], ...] = ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[BitVector[K], BitVector[V]]](
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
