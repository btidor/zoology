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
from typing import Callable, ClassVar, Self, override

from .theory_bitvec import BTerm, BValue
from .theory_core import BaseTerm, CValue, DumpContext, Eq


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
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)


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
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self


@dataclass(frozen=True, slots=True)
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

    @classmethod
    def simplify(cls, array: ATerm, key: BTerm, call: Callable[..., Self]) -> BTerm:
        match array:
            case ASymbol():
                return call(array, key)
            case AValue(val):
                return val
            case Store(base, lower, upper):
                pass
            case _:
                raise TypeError(f"unexpected ATerm: {array.__class__}")
        for k, v in reversed(upper):
            match Eq(k, key):
                case CValue(True):  # pyright: ignore[reportUnnecessaryComparison]
                    return v
                case CValue(False):  # pyright: ignore[reportUnnecessaryComparison]
                    continue
                case _:
                    return call(copy.deepcopy(array), key)
        match key:
            case BValue(s):
                if s in lower:
                    return lower[s]
                else:
                    match base:
                        case AValue(default):
                            return default
                        case ASymbol() as symbol:
                            return call(symbol, key)
            case _:
                return call(Store(base, copy.copy(lower)), key)


@dataclass(frozen=True, slots=True)
class Store(ATerm):
    base: ASymbol | AValue
    lower: dict[int, BTerm] = field(default_factory=dict[int, BTerm])
    upper: list[tuple[BTerm, BTerm]] = field(default_factory=list[tuple[BTerm, BTerm]])

    # Warning: Store is not actually immutable! Take care to create a deep copy
    # when reusing a Store in Selects and other expressions.
    __copy__ = None  # pyright: ignore[reportAssignmentType]
    __deepcopy__ = None  # pyright: ignore[reportAssignmentType]

    # Also note that `Store.descendants` is likely incorrect.

    def width(self) -> tuple[int, int]:
        return self.base.width()

    @override
    def dump(self, ctx: DumpContext) -> None:
        writes = list[tuple[BTerm, BTerm]](
            [(BValue(k, self.base.key), v) for k, v in self.lower.items()]
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
