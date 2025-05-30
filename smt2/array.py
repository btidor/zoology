"""
Definitions for the theory of arrays.

Up-to-date with SMT-LIB version 2.7, QF_ABV logic.

See: https://smt-lib.org/theories-ArraysEx.shtml
"""
# ruff: noqa

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import ClassVar, override

from .core import DumpContext, Symbolic
from . import bv


@dataclass(frozen=True, slots=True)
class Array[K: int, V: int](Symbolic):
    def reveal(self) -> dict[int, int] | None:
        return None


@dataclass(frozen=True, slots=True)
class Symbol[K: int, V: int](Array[K, V]):
    name: bytes
    key: K
    value: V

    def dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self.name,
            (
                b"(declare-fun %s () (_ Array (_ BitVec %d) (_ BitVec %d)))"
                % (self.name, self.key, self.value)
            ),
        )
        ctx.write(self.name)


@dataclass(frozen=True, slots=True)
class Value[K: int, V: int](Array[K, V]):
    default: bv.BitVector[V]
    key: K
    value: V

    def dump(self, ctx: DumpContext) -> None:
        ctx.write(
            b"((_ as const (Array (_ BitVec %d) (_ BitVec %d)))"
            % (self.key, self.value)
        )
        self.default.dump(ctx)
        ctx.write(b")")

    @override
    def reveal(self) -> dict[int, int] | None:
        if (d := self.default.reveal()) is None:
            return None
        return defaultdict(lambda: d)


@dataclass(frozen=True, slots=True)
class Select[K: int, V: int](Array[K, V]):
    op: ClassVar[bytes] = b"select"
    array: Array[K, V]
    key: bv.BitVector[K]


@dataclass(frozen=True, slots=True)
class Store[K: int, V: int](Array[K, V]):
    op: ClassVar[bytes] = b"store"
    array: Array[K, V]
    key: bv.BitVector[K]
    value: bv.BitVector[V]
