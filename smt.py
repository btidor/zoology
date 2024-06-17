"""A library of augmentations for zbitvector."""

# pyright: reportPrivateUsage=false

from __future__ import annotations

from itertools import batched
from typing import (
    Any,
    Literal,
    TypeAlias,
    cast,
)

from Crypto.Hash import keccak
from zbitvector import Array, Constraint, Int, Solver, Symbolic, Uint
from zbitvector._bitwuzla import BZLA, BitwuzlaTerm, Kind

Uint8: TypeAlias = Uint[Literal[8]]
Uint52: TypeAlias = Uint[Literal[52]]
Uint64: TypeAlias = Uint[Literal[64]]
Uint160: TypeAlias = Uint[Literal[160]]
Uint256: TypeAlias = Uint[Literal[256]]

type Expression = "Symbolic | Array[Any, Any]"
type Bitvec = Uint[Any] | Int[Any]


def _make_symbolic[S: Expression](cls: type[S], term: Any) -> S:
    instance = cls.__new__(cls)
    instance._term = term  # type: ignore
    return instance


def _from_expr[S: Expression](cls: type[S], kind: Kind, *args: Expression) -> S:
    return cls._from_expr(kind, *args)  # type: ignore


def _term(expr: Expression) -> BitwuzlaTerm:
    return expr._term  # type: ignore


def make_uint(n: int) -> type[Uint[Any]]:
    """Create a new UintN class from a given N."""
    return Uint[Literal[n]]  # type: ignore


def explode_bytes(word: Uint256) -> list[Uint8]:
    """Explode a Uint256 into a list of Uint8s."""
    result = list[Uint8]()
    for i in range(0, 256, 8):
        term = BZLA.mk_term(Kind.BV_EXTRACT, (_term(word),), (i + 7, i))
        result.append(_make_symbolic(Uint8, term))
    return result


def concat_bytes(*args: Uint8) -> Uint[Any]:
    """Concatenate a series of Uint8s into a longer UintN."""
    if len(args) == 1:
        return args[0]
    uint = make_uint(len(args) * 8)
    term = BZLA.mk_term(Kind.BV_CONCAT, tuple(_term(a) for a in args))
    return _make_symbolic(uint, term)


def concat_words(*args: Uint256) -> Uint[Any]:
    """Concatenate a series of Uint256s into a longer UintN."""
    uint = make_uint(len(args) * 256)
    term = BZLA.mk_term(Kind.BV_CONCAT, tuple(_term(a) for a in args))
    return _make_symbolic(uint, term)


def implies(a: Constraint, b: Constraint) -> Constraint:
    """Return a constraint asserting that a implies b."""
    return _from_expr(Constraint, Kind.IMPLIES, a, b)


def iff(a: Constraint, b: Constraint) -> Constraint:
    """Return a constraint asserting that a iff b."""
    return _from_expr(Constraint, Kind.IFF, a, b)


def prequal(a: Uint[Any], b: Uint[Any]) -> bool:
    """Check if a == b after preprocessing without calling the solver."""
    if a.width != b.width:
        return False
    return (a == b).reveal() or False


def bvlshr_harder[N: int](value: Uint[N], shift: Uint[N]) -> Uint[N]:
    """Return `(bvlshr value shift)` with better preprocessing."""
    default = value >> shift
    if default.reveal() is not None or (n := shift.reveal()) is None or n == 0:
        return default

    term = _term(value)
    prefix = BZLA.mk_bv_value(BZLA.mk_bv_sort(n), 0)
    while n > 0:
        if term.get_kind() == Kind.BV_CONCAT:
            term, addon = term.get_children()
            n -= addon.get_sort().bv_get_size()
            if n < 0:
                return default
        elif term.get_kind() == Kind.VAL:
            z = term.get_sort().bv_get_size()
            if z <= n:
                return value.__class__(0)
            term = BZLA.mk_term(Kind.BV_EXTRACT, (term,), (z - 1, n))
            break
        else:
            return default
    return _make_symbolic(value.__class__, BZLA.mk_term(Kind.BV_CONCAT, (prefix, term)))


# Keccak-256


def concrete_hash(data: bytes | str) -> Uint256:
    """Hash a concrete input and return the digest as a Uint256."""
    encoded = data if isinstance(data, bytes) else data.encode()
    digest = keccak.new(data=encoded, digest_bits=256).digest()
    return Uint256(int.from_bytes(digest))


EMPTY_DIGEST = concrete_hash(b"")

# Substitution

type Substitutions = list[tuple[Expression, Expression]]


def substitutions[R](before: R, after: R) -> Substitutions:
    """Extract substitution pairs from the given state objects."""
    subs: Substitutions = []
    if not hasattr(before, "__dict__"):
        return subs
    for k, v in before.__dict__.items():
        w = after.__dict__[k]
        if isinstance(v, Symbolic) or isinstance(v, Array):
            subs.append((cast(Any, v), w))
        elif hasattr(v, "__substitutions__"):
            subs.extend(zip(v.__substitutions__(), w.__substitutions__()))
    return subs


def substitute[R](item: R, subs: Substitutions) -> R:
    """Perform term substitution according to the given map."""
    if len(subs) == 0:
        return item
    match item:
        case Symbolic() | Array():
            return _make_symbolic(
                item.__class__,  # type: ignore
                BZLA.substitute(
                    _term(item),  # type: ignore
                    dict((_term(k), _term(v)) for k, v in subs),
                ),
            )
        case list():
            return [substitute(r, subs) for r in item]  # type: ignore
        case tuple():
            return tuple(substitute(r, subs) for r in item)  # type: ignore
        case dict():
            return dict((k, substitute(v, subs)) for k, v in item.items())  # type: ignore
        case _:
            if not hasattr(item, "__dict__"):
                return item
            result = item.__new__(item.__class__)
            for k, v in item.__dict__.items():
                object.__setattr__(result, k, substitute(v, subs))
            return result


# Compaction


def compact_zarray(
    solver: Solver, constraint: Constraint, array: Array[Uint256, Uint8]
) -> Constraint:
    """Simplify array keys using the given solver's contraints."""
    assert solver.check()
    term = _term(array)
    ksort = term.get_sort().array_get_index()

    writes = list[tuple[BitwuzlaTerm, BitwuzlaTerm, BitwuzlaTerm]]()
    while term.get_kind() == Kind.ARRAY_STORE:
        term, key, value = term.get_children()
        key_ = BZLA.mk_bv_value(ksort, int(BZLA.get_value_str(key), 2))
        writes.append((key, value, key_))
    writes.reverse()

    for batch in batched(writes, 256):
        for key, _, key_ in batch:
            constraint &= _make_symbolic(
                Constraint, BZLA.mk_term(Kind.EQUAL, (key, key_))
            )
        if solver.check(~constraint):
            raise NotImplementedError  # check writes one by one
        else:
            for _, value, key_ in batch:
                term = BZLA.mk_term(Kind.ARRAY_STORE, (term, key_, value))

    array._term = term  # type: ignore
    return constraint


def compact_helper[N: int](
    solver: Solver, constraint: Constraint, term: Uint[N], concrete: Uint[N]
) -> tuple[Constraint, Uint[N]]:
    """Select between original and concretized versions of a term."""
    extended = constraint & (term == concrete)
    if solver.check(~extended):
        return constraint, term
    else:
        return extended, concrete


# Misc.


class NarrowingError(Exception):
    """
    Applying deferred constraints failed.

    Used when a branch satisifes path constraints but is unreachable in
    practice.
    """

    def __init__(self, key: bytes | None) -> None:
        """Create a new NarrowingError."""
        self.key = key

    def __str__(self) -> str:
        return self.key.hex() if self.key else "unknown"
