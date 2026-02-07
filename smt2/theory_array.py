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
from typing import Any, ClassVar, Iterable, Self, override

from line_profiler import profile

from .bitwuzla import BZLA
from .theory_bitvec import BTerm, BValue
from .theory_core import (
    BaseTerm,
    BitwuzlaTerm,
    CValue,
    DumpContext,
    Eq,
    Kind,
    ReplaceContext,
    TermCategory,
    reverse_enumerate,
)


@dataclass(repr=False, slots=True, eq=False)
class ATerm(BaseTerm):
    def sort(self) -> bytes:
        return b"(Array (_ BitVec %d) (_ BitVec %d))" % self.width()

    @abc.abstractmethod
    def width(self) -> tuple[int, int]: ...


@dataclass(repr=False, slots=True, eq=False)
class ASymbol(ATerm):
    name: bytes
    key: int
    value: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.value)

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def replace(self, model: ReplaceContext) -> BaseTerm:
        if (r := model.check(self)) is not None:
            return r
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, self.width())


@dataclass(repr=False, slots=True, eq=False)
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

    @override
    def children(self) -> Iterable[BTerm]:
        return (self.default,)

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

    @override
    def replace(self, model: ReplaceContext) -> BaseTerm:
        if (r := model.check(self)) is not None:
            return r
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.default.bzla, self.width())


@dataclass(repr=False, slots=True, eq=False)
class Select(BTerm):
    op: ClassVar[bytes] = b"select"
    kind: ClassVar[Kind] = Kind.ARRAY_SELECT
    array: ATerm
    key: BTerm

    @override
    def __post_init__(self) -> None:
        k, v = self.array.width()
        assert k == self.key.width
        self.width = v
        if isinstance(self.array, Store):
            self.array.freeze = True
        super(Select, self).__post_init__()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.array, self.key)

    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty and self._pretty == "safe_select":
            self.array.dump(ctx)
            ctx.write(b"[")
            self.key.dump(ctx)
            ctx.write(b"]")
            return
        super(Select, self).dump(ctx)


@dataclass(repr=False, slots=True, eq=False)
class Store(ATerm):
    op: ClassVar[bytes] = b"store"
    kind: ClassVar[Kind] = Kind.ARRAY_STORE
    category: ClassVar[TermCategory] = TermCategory.MUTABLE

    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])

    freeze: bool = field(init=False, default=False)

    # Warning: Store is not immutable by default! Take care to set `freeze=True`
    # when reusing a Store in Selects and other expressions. This will cause
    # `set` to make a copy the next time it's called, preventing further changes
    # to the current instance.

    def __copy__(self) -> Self:
        return copy.deepcopy(self)

    def __deepcopy__(self, memo: Any, /) -> Self:
        k = self.__new__(self.__class__)
        k.base = self.base
        k.lower = copy.copy(self.lower)
        k.upper = copy.copy(self.upper)
        k.freeze = False
        k.count = self.count
        k._bzla = self._bzla
        return k

    def width(self) -> tuple[int, int]:
        return self.base.width()

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (
            self.base,
            *self.lower.values(),
            *(k for k, _ in self.upper),
            *(v for _, v in self.upper),
        )

    @profile
    def set(self, key: BTerm, value: BTerm) -> Store:
        array = copy.deepcopy(self) if self.freeze else self
        array._bzla = None
        array._set(key, value)
        return array

    @profile
    def _set(self, key: BTerm, value: BTerm) -> None:
        for i, (k, v) in reverse_enumerate(self.upper):
            match Eq(k, key):
                case CValue(True):
                    self.upper[i] = (k, value)
                    self.count += value.count - v.count
                    return
                case CValue(False):
                    continue
                case _:
                    self.upper.append((key, value))
                    self.count += key.count + value.count + 2
                    return
        if isinstance(key, BValue):
            k = key.value
            if k in self.lower:
                self.count -= self.lower[k].count + 1
            self.lower[k] = value
            self.count += value.count + 1
        else:
            self.upper.append((key, value))
            self.count += key.count + value.count + 2

    @override
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty:
            ctx.write(b"{\n  ")
            self.base.dump(ctx)
            for k, v in self.lower.items():
                ctx.write(b"\n  " + hex(k).encode())
                ctx.write(b" -> ")
                v.dump(ctx)
            for k, v in self.upper:
                ctx.write(b"\n  ")
                k.dump(ctx)
                ctx.write(b"\n   -> ")
                v.dump(ctx)
            ctx.write(b"\n}")
        else:
            ctx.write(b"(store " * (len(self.lower) + len(self.upper)))
            self.base.dump(ctx)
            for k, v in self.lower.items():
                if self.base.key % 8 == 0:
                    ctx.write(
                        b" #x" + k.to_bytes(self.base.key // 8).hex().encode() + b" "
                    )
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

    # @override TODO
    # def replace(self, model: ReplaceContext) -> BaseTerm:
    #     raise NotImplementedError

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        term = self.base.bzla
        for k, v in self.lower.items():
            term = BZLA.mk_term(
                self.kind, (term, BZLA.mk_value(k, self.width()[0]), v.bzla)
            )
        for k, v in self.upper:
            term = BZLA.mk_term(self.kind, (term, k.bzla, v.bzla))
        return term
