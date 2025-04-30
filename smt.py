"""A library of augmentations for zbitvector."""

from __future__ import annotations

import copy
import re
from collections import defaultdict
from functools import reduce
from itertools import batched, repeat
from typing import Any, Literal, Self, overload

from Crypto.Hash import keccak
from zbitvector import Array, Constraint, Int, Symbolic, Uint
from zbitvector._bitwuzla import BZLA, BitwuzlaSort, BitwuzlaTerm, Kind

from xsolver import Client

Uint8 = Uint[Literal[8]]
Uint64 = Uint[Literal[64]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]

Uint128 = Uint[Literal[128]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

Int256 = Int[Literal[256]]

type Expression = Symbolic | Array[Any, Any]

Leading0s = re.compile(r"\A0{64}")
Leading1s = re.compile(r"\A1{64}")


def _make_symbolic[X: Expression](cls: type[X], term: BitwuzlaTerm) -> X:
    instance = cls.__new__(cls)
    instance._term = term  # type: ignore
    return instance


def _from_expr[S: Symbolic](cls: type[S], kind: Kind, *args: Expression) -> S:
    return cls._from_expr(kind, *args)  # type: ignore


def _term(x: Expression) -> BitwuzlaTerm:
    return x._term  # type: ignore


def _sort(cls: type[Symbolic]) -> BitwuzlaSort:
    return cls._sort  # type: ignore


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


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    """Return a constraint asserting that a + b does not overflow."""
    return ~_from_expr(Constraint, Kind.BV_UADD_OVERFLOW, a, b)


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    """Return a constraint asserting that a - b does not underflow."""
    return ~_from_expr(Constraint, Kind.BV_USUB_OVERFLOW, a, b)


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
    """
    Return `(bvlshr value shift)` with better preprocessing.

    This (best-effort!) helper breaks open `concat`s, inserts leading zeroes on
    the left, and discards terms that are shifted out on the right.
    """
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


def smart_arith(value: Uint256) -> tuple[Uint256, int | None]:
    """
    Aggressively simplify an addition or subtraction operation.

    Intended for index arithmetic where a fixed term (memory offset) is
    subtracted out of an expression containing itself.
    """
    constant = 0
    terms = defaultdict[BitwuzlaTerm, int](lambda: 0)
    queue = [(_term(value), True)]
    while queue:
        term, msb = queue.pop()
        match term.get_kind():
            case Kind.VAL:
                v = int(BZLA.get_value_str(term), 2)
                constant += v if msb else -v
            case Kind.BV_ADD:
                queue.extend((t, msb) for t in term.get_children())
            case Kind.BV_NOT:
                term = term.get_children()[0]
                constant += -1 if msb else 1
                queue.append((term, not msb))
            case _:
                terms[term] += 1 if msb else -1

    additions, removals = list[BitwuzlaTerm](), list[BitwuzlaTerm]()
    constant %= 2**value.width
    term = BZLA.mk_bv_value(_term(value).get_sort(), constant)
    additions.append(term)
    if constant == 0:
        zeroes, ones = True, True
    elif constant < 2 ** (value.width - 1):
        zeroes, ones = True, False
    else:
        zeroes, ones = False, True

    for term, count in terms.items():
        if count == 0:
            continue

        prefix = _quick_prefix(term)
        if prefix is None:
            zeroes, ones = False, False
        else:
            if not Leading0s.match(prefix):
                if count > 0:
                    zeroes = False
                else:
                    ones = False
            if not Leading1s.match(prefix):
                if count > 0:
                    ones = False
                else:
                    zeroes = False

        if count > 0:
            additions.extend(repeat(term, count))
        else:
            removals.extend(repeat(term, -count))

    term = _bvsum256(additions)
    if removals:
        term = BZLA.mk_term(Kind.BV_SUB, (term, _bvsum256(removals)))

    if zeroes:
        msb = 0
    elif ones:
        msb = 1
    else:
        msb = None

    return _make_symbolic(Uint256, term), msb


def _bvsum256(values: list[BitwuzlaTerm]) -> BitwuzlaTerm:
    """Compute the sum of a list of 256-bit bitvectors."""
    match len(values):
        case 0:
            return BZLA.mk_bv_value(_sort(Uint256), 0)
        case 1:
            return values[0]
        case _:
            return BZLA.mk_term(Kind.BV_ADD, values)


def smart_cmp(constraint: Constraint) -> bool | None:
    """
    Aggressively simplify an equality operation.

    Uses `quick_msb()` to check if the high bits differ. Returns False if the
    term definitively simplifies to False, otherwise None.
    """
    term = _term(constraint)
    if term.get_kind() != Kind.EQUAL:
        return None

    lterm, rterm = term.get_children()
    if (a := _quick_prefix(lterm)) is None:
        return None
    elif (b := _quick_prefix(rterm)) is None:
        return None
    elif a == b:
        return None  # didn't compare other digits, so unknown
    return False


def _quick_prefix(term: BitwuzlaTerm) -> str | None:
    """
    Quickly extract the concrete prefix of the given term, if available.

    Handles concrete values and simple `concat`s. To avoid performance issues,
    does *not* descend into nested `concat`s.
    """
    match term.get_kind():
        case Kind.VAL:
            return BZLA.get_value_str(term)
        case Kind.BV_CONCAT:
            term, _ = term.get_children()
            if term.get_kind() == Kind.VAL:
                return BZLA.get_value_str(term)
        case _:
            pass


def get_constants(s: Symbolic | BitwuzlaTerm) -> dict[str, BitwuzlaTerm]:
    """Recursively search the term for constants."""
    constants = dict[str, BitwuzlaTerm]()
    visited = set[BitwuzlaTerm]()
    queue = set([_term(s) if isinstance(s, Symbolic) else s])
    while queue:
        item = queue.pop()
        if item in visited:
            continue
        queue.update(item.get_children())
        if item.is_const():
            assert (sym := item.get_symbol()) is not None
            constants[sym] = item
        visited.add(item)
    return constants


def substitute[S: Symbolic](s: S, replacements: dict[BitwuzlaTerm, Expression]) -> S:
    """Perform term substitution according to the given map."""
    if len(replacements) == 0:
        return s
    return _make_symbolic(
        s.__class__,
        BZLA.substitute(_term(s), dict((k, _term(v)) for k, v in replacements.items())),
    )


def substitute2[S: Symbolic, N: int](s: S, replacements: dict[Uint[N], Uint[N]]) -> S:
    """Perform term substitution according to the given map."""
    if len(replacements) == 0:
        return s
    return _make_symbolic(
        s.__class__,
        BZLA.substitute(
            _term(s), dict((_term(k), _term(v)) for k, v in replacements.items())
        ),
    )


def compact_array(
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


def describe(bv: Uint[Any] | int) -> str:
    """
    Produce a human-readable description of the given bitvector.

    For concrete bitvectors, returns a result in hexadecimal. Long values are
    broken into 256-bit chunks using dot syntax, e.g. "0x[1234.1]".

    For symbolic bitvectors, returns a hash based on the input variables.
    """
    v = bv if isinstance(bv, int) else bv.reveal()
    if v is not None:
        if v < (1 << 256):
            return hex(v)
        p = list[str]()
        while v > 0:
            b = v & ((1 << 256) - 1)
            p.append(hex(b)[2:])
            v >>= 256
        return f"0x[{'.'.join(reversed(p))}]"
    else:
        assert isinstance(bv, Uint)
        keys = sorted(get_constants(bv).keys())
        digest = keccak.new(
            data=_term(bv).dump("smt2").encode(), digest_bits=256
        ).digest()
        return f"[{','.join(keys)}]#{digest[:3].hex()}"


class ConstrainingError(Exception):
    """Applying hard or soft constraints failed."""

    pass


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


class Solver:
    """A custom replacement for zbitvector.Solver."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraint = Constraint(True)
        self._client = Client()
        self._last_check = False
        self._pending = Constraint(True)
        self._dirty = False

    def __deepcopy__(self, memo: Any) -> Self:
        result = self.__new__(self.__class__)
        result.constraint = self.constraint
        result._client = self._client
        result._last_check = self._last_check
        result._pending = self._pending
        result._dirty = True
        self._dirty = True
        return result

    def add(self, assertion: Constraint) -> None:
        """Assert the given constraint."""
        self.constraint &= assertion
        self._last_check = False
        self._pending &= assertion

    def check(self, *assumptions: Constraint, force: bool = True) -> bool:
        """Check whether the constraints are satifiable."""
        q = reduce(Constraint.__and__, assumptions, Constraint(True))
        if (r := (self.constraint & q).reveal()) is not None and not force:
            # HACK: with the solver in an external process, it's slow to call
            # check(). So we defer calling the solver for trivial cases, but
            # save the constraint in case the caller later calls evaluate().
            self._last_check = q
            return r

        if self._dirty:
            self._client = copy.deepcopy(self._client)
            self._dirty = False

        self._client.assert_term(_term(self._pending))
        self._pending = Constraint(True)

        self._last_check = self._client.check(_term(q))
        return self._last_check

    @overload
    def evaluate(self, s: Constraint) -> bool: ...

    @overload
    def evaluate(self, s: Uint[Any]) -> int: ...

    @overload
    def evaluate(self, s: Array[Any, Any]) -> dict[int, int]: ...

    def evaluate(
        self, s: Constraint | Uint[Any] | Array[Any, Any]
    ) -> bool | int | dict[int, int]:
        """Backdoor method for evaluating non-bitvectors."""
        if isinstance(self._last_check, Constraint):
            self.check(self._last_check, force=True)
            assert isinstance(self._last_check, bool)
        if not self._last_check:
            raise ValueError("solver is not ready for model evaluation")

        val = self._client.evaluate(_term(s))
        match s:
            case Constraint():
                assert val == 0 or val == 1, f"not boolean: {val}"
                return bool(val)
            case Uint():
                assert isinstance(val, int)
                return val
            case Array():
                assert isinstance(val, dict)
                return val
