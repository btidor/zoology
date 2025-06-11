"""
Definitions for the theory of arrays.

Up-to-date with SMT-LIB version 2.7, QF_ABV logic.

See: https://smt-lib.org/theories-ArraysEx.shtml
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import dataclass
from typing import ClassVar, override

from .theory_bitvec import BTerm, BValue
from .theory_core import BaseTerm, DumpContext


@dataclass(frozen=True, slots=True)
class ATerm(BaseTerm):
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

    @override
    def substitute(self, subs: dict[BaseTerm, BaseTerm]) -> BaseTerm:
        if self in subs:
            return subs[self]
        return self


@dataclass(frozen=True, slots=True)
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
    def substitute(self, subs: dict[BaseTerm, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, slots=True)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    array: ATerm
    key: BTerm

    @override
    def __post_init__(self) -> None:
        k, v = self.array.width()
        assert k == self.key.width
        object.__setattr__(self, "width", v)

    @classmethod
    def simplify(cls, array: ATerm, key: BTerm) -> BTerm | None:
        match array, key:
            case AValue(de), _:
                return de
            case Store(base, lo, up), _ if not lo and not up:
                return cls.simplify(base, key)
            case Store(base, lo, up), BValue(kval) if not up:
                for k, v in lo:
                    if k == kval:
                        return v
                return cls.simplify(base, key)
            case _:
                return None


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
