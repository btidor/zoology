"""A library of augmentations for zbitvector."""

# pyright: reportPrivateUsage=false

from __future__ import annotations

import copy
from functools import reduce
from itertools import batched
from typing import Any, Iterable, Literal, Self, overload

from Crypto.Hash import keccak
from zbitvector import Array as zArray
from zbitvector import Constraint, Int, Symbolic, Uint
from zbitvector._bitwuzla import BZLA, BitwuzlaTerm, Kind

from xsolver import Client

Uint8 = Uint[Literal[8]]
Uint64 = Uint[Literal[64]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]

Uint52 = Uint[Literal[52]]
Uint128 = Uint[Literal[128]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

Int256 = Int[Literal[256]]

type Expression = Symbolic | zArray[Any, Any]


def _make_symbolic[X: Expression](
    cls: type[X], term: BitwuzlaTerm | list[BitwuzlaTerm]
) -> X:
    # TODO: it's not actually possible for `term` to be a list[BitwuzlaTerm];
    # that's due to a bug in the zbitvector types.
    instance = cls.__new__(cls)
    instance._term = term  # type: ignore
    return instance


def _from_expr[S: Symbolic](cls: type[S], kind: Kind, *args: Expression) -> S:
    return cls._from_expr(kind, *args)  # type: ignore


def _term(x: Expression) -> BitwuzlaTerm:
    return x._term  # type: ignore


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


def compact_zarray(
    solver: Solver, constraint: Constraint, array: zArray[Uint256, Uint8]
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


class Array[K: Uint[Any], V: Uint[Any]](zArray[K, V]):
    """A wrapper around zbitvector.Array. Supports read and write tracking."""

    def __init__(self, value: V | str, /) -> None:
        """Create a new Array."""
        super().__init__(value)
        self.accessed = list[K]()
        self.written = list[K]()

    def __deepcopy__(self, memo: Any) -> Self:
        result = super().__deepcopy__(memo)
        result.accessed = copy.copy(self.accessed)
        result.written = copy.copy(self.written)
        return result

    def clone_and_reset(self) -> Self:
        """Clone this Array and reset access tracking."""
        result = super().__deepcopy__(None)
        result.accessed = []
        result.written = []
        return result

    def __getitem__(self, key: K) -> V:
        """Look up the given symbolic key."""
        self.accessed.append(key)
        return self.peek(key)

    def __setitem__(self, key: K, value: V) -> None:
        """Set the given symbolic key to the given symbolic value."""
        self.written.append(key)
        self.poke(key, value)

    def peek(self, key: K) -> V:
        """Look up the given symbolic key, but don't track the lookup."""
        return super().__getitem__(key)

    def poke(self, key: K, value: V) -> None:
        """Set the given symbolic key, but don't track the write."""
        super().__setitem__(key, value)

    def printable_diff(
        self, name: str, solver: Solver, original: Array[K, V]
    ) -> Iterable[str]:
        """
        Evaluate a diff of this array against another.

        Yields a human-readable description of the differences.
        """
        diffs: list[tuple[str, list[tuple[K, V, V | None]]]] = [
            ("R", [(key, original.peek(key), None) for key in self.accessed]),
            (
                "W",
                [(key, self.peek(key), original.peek(key)) for key in self.written],
            ),
        ]
        line = name

        for prefix, rows in diffs:
            concrete = dict[str, tuple[str, str | None]]()
            for key, value, prior in rows:
                k = describe(solver.evaluate(key))
                v = describe(solver.evaluate(value))
                p = describe(solver.evaluate(prior)) if prior is not None else None
                if v != p:
                    concrete[k] = (v, p)

            for k in sorted(concrete.keys()):
                line += f"\t{prefix}: {k} "
                if len(k) > 34:
                    yield line
                    line = "\t"
                v, p = concrete[k]
                line += f"-> {v}"
                if p is not None:
                    if len(v) > 34:
                        yield line
                        line = "\t  "
                    line += f" (from {p})"
                yield line
                line = ""

        if line == "":
            yield ""


class Solver:
    """A custom replacement for zbitvector.Solver."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraint = Constraint(True)
        self._client = Client()
        self._last_check = False

    def add(self, assertion: Constraint) -> None:
        """Assert the given constraint."""
        self._last_check = False
        self.constraint &= assertion
        self._client.assert_term(_term(assertion))

    def check(self, *assumptions: Constraint, force: bool = True) -> bool:
        """Check whether the constraints are satifiable."""
        q = reduce(Constraint.__and__, assumptions, Constraint(True))
        if (r := (self.constraint & q).reveal()) is not None and not force:
            # HACK: with the solver in an external process, it's slow to call
            # check(). So we defer calling the solver for trivial cases, but
            # save the constraint in case the caller later calls evaluate().
            self._last_check = q
            return r

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

        match s:
            case Constraint() | Array():
                raise NotImplementedError
            case Uint():
                return self._client.evaluate(_term(s))
