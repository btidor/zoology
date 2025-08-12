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

from .theory_bitvec import BTerm, BValue
from .theory_core import BZLA, CACHE, BaseTerm, BitwuzlaTerm, DumpContext, Kind


@dataclass(repr=False, slots=True, unsafe_hash=True)
class ATerm(BaseTerm):
    def sort(self) -> bytes:
        return b"(Array (_ BitVec %d) (_ BitVec %d))" % self.width()

    @abc.abstractmethod
    def width(self) -> tuple[int, int]: ...


@dataclass(repr=False, slots=True, unsafe_hash=True)
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
    def bzla(self) -> BitwuzlaTerm:
        global CACHE
        if self.name not in CACHE:
            CACHE[self.name] = BZLA.mk_const(
                BZLA.mk_array_sort(
                    BZLA.mk_bv_sort(self.key), BZLA.mk_bv_sort(self.value)
                ),
                self.name.decode(),
            )
        return CACHE[self.name]


@dataclass(repr=False, slots=True, unsafe_hash=True)
class AValue(ATerm):
    default: BTerm
    key: int

    def width(self) -> tuple[int, int]:
        return (self.key, self.default.width)

    @override
    def children(self) -> Iterable[BaseTerm]:
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
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_const_array(
                BZLA.mk_array_sort(
                    BZLA.mk_bv_sort(self.key), BZLA.mk_bv_sort(self.default.width)
                ),
                self.default.bzla(),
            )
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
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
            self.array.copied = True
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

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.array.bzla(), self.key.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Store(ATerm):
    op: ClassVar[bytes] = b"store"
    kind: ClassVar[Kind] = Kind.ARRAY_STORE
    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])
    copied: bool = field(init=False, default=False)

    def __post_init__(self) -> None:
        assert not self.lower and not self.upper
        self._bzla = self.base.bzla()
        super(Store, self).__post_init__()

    # Warning: Store is not immutable by default! Take care to set `copied=True`
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
        k.copied = False
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
        array = copy.deepcopy(self) if self.copied else self
        array._set(key, value)
        return array

    @profile
    def _set(self, key: BTerm, value: BTerm) -> None:
        if isinstance(key, BValue) and not self.upper:
            k = key.value
            if k in self.lower:
                self.count -= self.lower[k].count + 1
            self.lower[k] = value
            self.count += value.count + 1
        else:
            self.upper.append((key, value))
            self.count += key.count + value.count + 2
        assert self._bzla is not None
        self._bzla = BZLA.mk_term(self.kind, (self._bzla, key.bzla(), value.bzla()))

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(store " * (len(self.lower) + len(self.upper)))
        self.base.dump(ctx)
        for k, v in self.lower.items():
            if ctx.pretty:
                ctx.write(hex(self.base.key).encode())
            elif self.base.key % 8 == 0:
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

    @override
    def bzla(self) -> BitwuzlaTerm:
        assert self._bzla is not None
        return self._bzla
