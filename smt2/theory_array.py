"""
Definitions for the theory of arrays.

Up-to-date with SMT-LIB version 2.7, QF_ABV logic.

See: https://smt-lib.org/theories-ArraysEx.shtml
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
import copy
from dataclasses import dataclass, field
from typing import Any, ClassVar, Self, override

from .theory_bitvec import BTerm, BValue
from .theory_core import BaseTerm, DumpContext


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
        # Because Select is special-cased in RewriteMeta, we're responsible for
        # setting our own min and max.
        object.__setattr__(self, "min", 0)
        object.__setattr__(self, "max", (1 << v) - 1)
        if isinstance(self.array, Store):
            object.__setattr__(self, "array", copy.deepcopy(self.array))


@dataclass(frozen=True, repr=False, slots=True)
class Store(ATerm):
    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])

    # Warning: Store is not actually immutable! Take care to create a deep copy
    # when reusing a Store in Selects and other expressions.
    __copy__ = None  # pyright: ignore[reportAssignmentType]

    def __deepcopy__(self, memo: Any, /) -> Self:
        k = self.__new__(self.__class__)
        object.__setattr__(k, "base", self.base)
        object.__setattr__(k, "lower", copy.copy(self.lower))
        object.__setattr__(k, "upper", copy.copy(self.upper))
        object.__setattr__(k, "descendants", self.descendants)
        return k

    # Also note that `Store.descendants` is likely incorrect.

    def width(self) -> tuple[int, int]:
        return self.base.width()

    def set(self, key: BTerm, value: BTerm) -> None:
        descendants = self.descendants
        if isinstance(key, BValue) and not self.upper:
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
