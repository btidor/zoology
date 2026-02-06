"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

from functools import reduce
from typing import Literal, overload

from smt2 import Array, Constraint, Int, Symbolic, Uint
from smt2.bitwuzla import BZLA
from smt2.composite import (
    ASymbol,
    And,
    BSymbol,
    BValue,
    CSymbol,
    Eq,
    Ite,
    Not,
    Select,
    Ult,
)
from smt2.theory_core import BaseTerm, DumpContext


Uint8 = Uint[Literal[8]]
Uint64 = Uint[Literal[64]]
Uint128 = Uint[Literal[128]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

Int256 = Int[Literal[256]]
Int257 = Int[Literal[257]]


class NarrowingError(Exception):
    pass


class ConstrainingError(Exception):
    pass


checks = 0


class Solver:
    __slots__ = (
        "constraint",
        "_minmax",
        "_last_check",
        "_last_assertion",
        "_replace_cache",
    )
    constraint: Constraint
    _minmax: dict[BaseTerm, tuple[int, int]]
    _last_check: bool
    _last_assertion: Constraint | None
    _replace_cache: dict[BaseTerm, BaseTerm]

    def __init__(self) -> None:
        self.constraint = Constraint(True)
        self._last_check = False
        self._last_assertion = None
        self._replace_cache = {}

    def add(self, assertion: Constraint, /) -> None:
        self._last_check = False
        self._last_assertion = assertion
        self._replace_cache.clear()
        if assertion.reveal() is True:
            return
        self.constraint &= assertion

    def replace[S: Symbolic](self, term: S, /) -> S:
        assert self._last_assertion is not None, "solver is not ready for replace"
        model = dict[BaseTerm, BaseTerm]()
        queue = [self._last_assertion._term]  # pyright: ignore[reportPrivateUsage]
        while queue:
            match queue.pop(0):
                case And(a, b):
                    queue.extend((a, b))
                case Eq(a, b):  # pyright: ignore[reportUnknownVariableType]
                    assert b not in model
                    model[b] = a
                case Ult(b, BValue(x)):
                    assert b not in model
                    if b.max > x - 1:
                        model[b] = b.realcopy(b.min, x - 1)
                case Not(Ult(b, BValue(x))):
                    assert b not in model
                    if b.min < x:
                        model[b] = b.realcopy(x, b.max)
                case _:
                    pass
        if model:
            return term.replace(model, self._replace_cache)
        else:
            return term

    def check(self, *assumptions: Constraint) -> bool:
        global checks, last_solver
        checks += 1
        self._last_check = False
        self._last_assertion = None

        constraint = reduce(Constraint.__and__, assumptions, self.constraint)
        r = BZLA.check(self, constraint._term)  # pyright: ignore[reportPrivateUsage]
        self._last_check = r
        return r

    @overload
    def evaluate(self, s: Constraint, /) -> bool: ...

    @overload
    def evaluate[N: int](self, s: Uint[N], /) -> int: ...

    @overload
    def evaluate[N: int, M: int](
        self, s: Array[Uint[N], Uint[M]], /
    ) -> dict[int, int]: ...

    def evaluate[N: int, M: int](
        self, sym: Constraint | Uint[N] | Array[Uint[N], Uint[M]], /
    ) -> bool | int | dict[int, int]:
        assert self._last_check is True and BZLA.last_solver is self, (
            "solver is not ready for model evaluation"
        )
        v = BZLA.get_value_str(sym._term)  # pyright: ignore[reportPrivateUsage]
        match sym:
            case Constraint():
                assert isinstance(v, str)
                return v == "1"
            case Uint():
                assert isinstance(v, str)
                return int(v, 2)
            case Array():
                assert isinstance(v, dict)
                d = dict[int, int]()
                for p, q in v.items():
                    d[int(p, 2)] = int(q, 2)
                return d


ZERO = Uint[Literal[8]](0)


def safe_get[K: int](
    key: Uint[K], value: Uint[Literal[8]], length: Uint[K]
) -> Uint[Literal[8]]:
    if isinstance(value._term, Select):  # pyright: ignore[reportPrivateUsage]
        value._term._pretty = "safe_select"  # pyright: ignore[reportPrivateUsage]
    res = (key < length).ite(value, ZERO)
    if isinstance((term := res._term), Ite):  # pyright: ignore[reportPrivateUsage]
        term._pretty = "safe_get"  # pyright: ignore[reportPrivateUsage]
    return res


def describe[N: int](s: Uint[N]) -> str:
    raise NotImplementedError("describe")


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return (a.into(Uint257) + b.into(Uint257)).into(Int257) >= Int257(0)


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return a >= b


def get_symbols(s: Symbolic) -> dict[bytes, type[Symbolic]]:
    ctx = DumpContext()
    ctx.prepare(s._term)  # pyright: ignore[reportPrivateUsage]
    symbols = dict[bytes, type[Symbolic]]()
    for k, v in ctx.symbols.items():
        match v:
            case CSymbol():
                symbols[k] = Constraint
            case BSymbol():
                symbols[k] = Uint[v.width]
            case ASymbol():
                symbols[k] = Array[Uint[v.key], Uint[v.value]]
            case _:
                raise TypeError(f"unexpected symbol: {v}")
    return symbols


def to_signed(width: int, value: int) -> int:
    if value & (1 << (width - 1)):
        return -((((1 << width) - 1) ^ value) + 1)
    return value


def to_unsigned(width: int, value: int) -> int:
    if value < 0:
        return (((1 << width) - 1) ^ -value) + 1
    return value
