"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

from functools import reduce
from typing import Literal, overload

from smt2 import Array, Constraint, Int, Symbolic, Uint
from smt2.composite import ASymbol, BSymbol, CSymbol, Ite, Select
from smt2.theory_core import DumpContext, BZLA, Result


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
last_solver: Solver | None = None


class Solver:
    __slots__ = ("constraint", "_last_check")
    constraint: Constraint
    _last_check: bool

    def __init__(self) -> None:
        self.constraint = Constraint(True)
        self._last_check = False

    def add(self, assertion: Constraint, /) -> None:
        self._last_check = False
        self.constraint &= assertion

    def check(self, *assumptions: Constraint) -> bool:
        global checks, last_solver
        checks += 1
        last_solver = self
        self._last_check = False

        constraint = reduce(Constraint.__and__, assumptions, self.constraint)
        BZLA.assume_formula(constraint._term.bzla())  # pyright: ignore[reportPrivateUsage]
        match BZLA.check_sat():
            case Result.SAT:
                self._last_check = True
                return True
            case Result.UNSAT:
                return False
            case Result.UNKNOWN:
                raise RuntimeError

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
        global last_solver
        assert self._last_check is True and last_solver is self, (
            "solver is not ready for model evaluation"
        )
        v = BZLA.get_value_str(sym._term.bzla())  # pyright: ignore[reportPrivateUsage]
        match sym:
            case Constraint():
                return v == "1"
            case Uint():
                return int(v, 2)
            case Array():
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
