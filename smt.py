"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

from functools import reduce
from itertools import chain
from typing import Literal, overload

from smt2 import Array, Constraint, Int, Symbolic, Uint
from smt2.bitwuzla import BZLA
from smt2.composite import (
    ASymbol,
    And,
    BSymbol,
    BTerm,
    BValue,
    CSymbol,
    CTerm,
    CValue,
    Concat,
    Eq,
    Ite,
    Not,
    Select,
    Store,
    Ult,
)
from smt2.theory_core import DumpContext, ReplaceContext


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
    __slots__ = ("_committed", "_pending", "_last_check")

    _committed: set[CTerm]
    _pending: set[CTerm]
    _last_check: bool

    def __init__(self) -> None:
        self._committed = set()
        self._pending = set()
        self._last_check = False

    def add(self, assertion: Constraint, /) -> None:
        self._last_check = False
        queue = [assertion._term]  # pyright: ignore[reportPrivateUsage]
        while queue:
            match queue.pop(0):
                case And(a, b):
                    queue.extend((a, b))
                case Eq(BValue(x), Concat(terms)):
                    for a in reversed(terms):
                        self._pending.add(
                            Eq(a, BValue(x & ((1 << a.width) - 1), a.width))
                        )
                        x >>= a.width
                case other:
                    self._pending.add(other)

    def replace(self) -> ReplaceContext:
        model = ReplaceContext()
        self._last_check = False
        # TODO: do we need to replace within sibling terms?
        for term in self._pending:
            match term:
                case Eq(BTerm() as v, Select(ASymbol() as a, k)) | Eq(
                    Select(ASymbol() as a, k), BTerm() as v
                ):
                    if a in model.terms:
                        z = model.terms[a]
                        assert isinstance(z, Store)
                    else:
                        z = Store(a)
                    model.terms[a] = z.set(k, v)
                case Eq(BTerm() as v, Select(Store() as a, k)) | Eq(
                    Select(Store() as a, k), BTerm() as v
                ):
                    if a in model.terms:
                        z = model.terms[a]
                        assert isinstance(z, Store)
                    else:
                        z = a
                        z.freeze = True
                    model.terms[a] = z.set(k, v)
                case Eq(CTerm() as a, CTerm() as b) | Eq(BTerm() as a, BTerm() as b):
                    if b in model.terms:
                        pass  # probably a contradiction
                    else:
                        model.terms[b] = a
                case Not(Eq(BTerm() as a, BTerm() as b)):
                    if (p := model.terms.get(a)) is not None:
                        assert isinstance(p, BTerm)
                        p.exclusions.add(b)
                        if isinstance(b, BValue):
                            p.exclusions.add(b.value)
                    else:
                        model.terms[a] = a.realcopy(exclude=b)
                    if (q := model.terms.get(b)) is not None:
                        assert isinstance(q, BTerm)
                        q.exclusions.add(a)
                        if isinstance(a, BValue):
                            q.exclusions.add(a)
                    else:
                        model.terms[b] = b.realcopy(exclude=a)
                case Ult(b, BValue(x)):
                    assert b not in model.terms
                    if b.max > x - 1:
                        model.terms[b] = b.realcopy(max_=x - 1)
                case Not(Ult(b, BValue(x))):
                    assert b not in model.terms
                    if b.min < x:
                        model.terms[b] = b.realcopy(min_=x)
                case Not(inv):
                    model.terms[inv] = CValue(False)
                case item:
                    model.terms[item] = CValue(True)
        self._committed = set(c.replace(model) for c in self._committed)
        self._committed.update(self._pending)
        self._pending.clear()
        return model

    def check(self, *assumptions: Constraint) -> bool:
        global checks
        checks += 1
        self._last_check = False

        terms = set(a._term for a in assumptions)  # pyright: ignore[reportPrivateUsage]
        terms.update(self._committed)
        terms.update(self._pending)
        r = BZLA.check(self, *terms)
        self._last_check = r
        return r

    @property
    def constraint(self) -> Constraint:
        if not self._committed and not self._pending:
            return Constraint(True)
        r = Constraint.__new__(Constraint)
        r._term = reduce(And, chain(self._committed, self._pending))  # pyright: ignore[reportPrivateUsage]
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

    def pretty(self) -> str:
        ctx = DumpContext(pretty=True)
        queue = list(chain(self._committed, self._pending))
        while queue:
            match queue.pop(0):
                case And(a, b):
                    queue.extend((a, b))
                case item:
                    ctx.write(b"\n* ")
                    item.dump(ctx)
        return ctx.out.decode()


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
