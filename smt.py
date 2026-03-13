"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

from functools import reduce
from itertools import chain
from typing import Literal, cast, overload

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
    _pending: list[CTerm]
    _last_check: bool

    def __init__(self) -> None:
        self._committed = set()
        self._pending = list()
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
                        self._pending.append(
                            Eq(a, BValue(x & ((1 << a.width) - 1), a.width))
                        )
                        x >>= a.width
                case other:
                    self._pending.append(other)

    def replace(self) -> ReplaceContext:
        model = ReplaceContext()
        self._last_check = False
        # TODO: what happens when replacement results in new extractable term?
        while self._pending:
            term = self._pending.pop(0)
            if term == CValue(True):
                continue
            elif term in self._committed:
                continue
            assert term != CValue(False), f"TODO: handle unreachable states"
            m = self._extract(term, model)

            committed = set[CTerm]((term,))
            for pre in self._committed:
                post = pre.replace(m)
                assert isinstance(post, CTerm)
                committed.add(post)
            self._committed = committed
            self._pending = list(cast(CTerm, p.replace(model)) for p in self._pending)
        return model

    def _extract(self, term: CTerm, model: ReplaceContext) -> ReplaceContext:
        m = ReplaceContext()
        match term:
            case Eq(BTerm() as v, Select(a, k)) | Eq(Select(a, k), BTerm() as v):
                match a:
                    case ASymbol():
                        z = Store(a)
                    case Store():
                        z = a
                        z.freeze = True
                    case _:
                        raise NotImplementedError
                m.terms[a] = z.set(k, v)
                if a in model.terms:
                    z = model.terms[a]
                    assert isinstance(z, Store)
                    model.terms[a] = z.set(k, v)
                else:
                    model.terms[a] = m.terms[a]
            case Eq(CTerm() as a, CTerm() as b) | Eq(BTerm() as a, BTerm() as b):
                assert b not in model.terms
                m.terms[b] = a
                model.terms[b] = m.terms[b]
            case Not(Eq(BValue(v), BTerm() as b)) if v == b.min:
                assert b not in model.terms
                m.terms[b] = b.realcopy(min_=v + 1)
                model.terms[b] = m.terms[b]
            case Not(Eq(BValue(v), BTerm() as b)) if v == b.max:
                assert b not in model.terms
                m.terms[b] = b.realcopy(max_=v - 1)
                model.terms[b] = m.terms[b]
            case Not(Eq(BValue(v), BTerm() as b)):
                if (p := model.terms.get(b)) is not None:
                    assert isinstance(p, BTerm)
                    if p.exclusions is None:
                        p.exclusions = set()
                    p.exclusions.add(v)
                else:
                    model.terms[b] = b.realcopy(exclude=v)
                m.terms[b] = b.realcopy(exclude=v)
            case Ult(b, BValue(x)):
                assert b not in model.terms
                if b.max > x - 1:
                    m.terms[b] = b.realcopy(max_=x - 1)
                    model.terms[b] = m.terms[b]
            case Not(Ult(b, BValue(x))):
                assert b not in model.terms
                if b.min < x:
                    m.terms[b] = b.realcopy(min_=x)
                    model.terms[b] = m.terms[b]
            case Not(inv):
                m.terms[inv] = CValue(False)
                model.terms[inv] = m.terms[inv]
            case item:
                m.terms[item] = CValue(True)
                model.terms[item] = m.terms[item]
        return m

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

    def verbose(self) -> str:
        ctx = DumpContext(mode="verbose")
        for term in chain(self._committed, self._pending):
            ctx.write(b"\n* ")
            term.dump(ctx)
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
