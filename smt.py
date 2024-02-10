"""A library of augmentations for zbitvector."""

# pyright: reportPrivateUsage=false

from __future__ import annotations

import copy
from itertools import batched
from typing import Any, Iterable, Literal, Self, TypeAlias, TypeVar, Union, overload

from Crypto.Hash import keccak
from zbitvector import Array as zArray
from zbitvector import Constraint, Int, Solver, Symbolic, Uint, _bitwuzla
from zbitvector._bitwuzla import BZLA, OPTIMIZE, BitwuzlaTerm, Kind, _reset_solver

Uint8 = Uint[Literal[8]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]

Expression: TypeAlias = "Symbolic | zArray[Any, Any]"

N = TypeVar("N", bound=int)
S = TypeVar("S", bound=Expression)

K = TypeVar("K", bound=Union[Uint[Any], Int[Any]])
V = TypeVar("V", bound=Union[Uint[Any], Int[Any]])


def _make_symbolic(cls: type[S], term: Any) -> S:
    instance = cls.__new__(cls)
    instance._term = term  # type: ignore
    return instance


def _from_expr(cls: type[S], kind: Kind, *args: Expression) -> S:
    return cls._from_expr(kind, *args)  # type: ignore


def _reveal(term: BitwuzlaTerm) -> int | None:
    if term.is_bv_value():
        _reset_solver()
        return int(BZLA.get_value_str(term), 2)
    else:
        return None


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
    uint = make_uint(len(args) * 8)
    if not OPTIMIZE:
        term = BZLA.mk_term(Kind.BV_CONCAT, tuple(_term(a) for a in args))
        return _make_symbolic(uint, term)

    pending = list[
        BitwuzlaTerm | tuple[BitwuzlaTerm, list[BitwuzlaTerm], list[BitwuzlaTerm]]
    ]()
    for arg in args:
        if _term(arg).get_kind() != Kind.ITE:
            pending.append(_term(arg))
            continue
        cond, term1, term2 = _term(arg).get_children()
        if len(pending) == 0 or isinstance(pending[-1], BitwuzlaTerm):
            pending.append((cond, [term1], [term2]))
            continue
        prev, prev1, prev2 = pending[-1]
        eq = BZLA.mk_term(Kind.EQUAL, (prev, cond))

        if _reveal(eq) == 1:
            prev1.append(term1)
            prev2.append(term2)
        else:
            pending.append((cond, [term1], [term2]))

    converted = list[BitwuzlaTerm]()
    for arg in pending:
        if isinstance(arg, BitwuzlaTerm):
            converted.append(arg)
        else:
            cond, list1, list2 = arg
            term = BZLA.mk_term(
                Kind.ITE,
                (
                    cond,
                    BZLA.mk_term(Kind.BV_CONCAT, list1) if len(list1) > 1 else list1[0],
                    BZLA.mk_term(Kind.BV_CONCAT, list2) if len(list2) > 1 else list2[0],
                ),
            )
            converted.append(term)
    if len(converted) == 1:
        term = converted[0]
    else:
        term = BZLA.mk_term(Kind.BV_CONCAT, converted)
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


def get_constants(s: Symbolic) -> dict[str, BitwuzlaTerm]:
    """Recursively search the term for constants."""
    constants = dict[str, BitwuzlaTerm]()
    queue = set([_term(s)])
    while queue:
        item = queue.pop()
        queue.update(item.get_children())
        if item.is_const():
            assert (sym := item.get_symbol()) is not None
            constants[sym] = item
    return constants


def substitute(s: S, replacements: dict[BitwuzlaTerm, Expression]) -> S:
    """Perform term substitution according to the given map."""
    if len(replacements) == 0:
        return s
    return _make_symbolic(
        s.__class__,
        BZLA.substitute(_term(s), dict((k, _term(v)) for k, v in replacements.items())),
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
            raise NotImplementedError  # TODO: check writes one by one
        else:
            for _, value, key_ in batch:
                term = BZLA.mk_term(Kind.ARRAY_STORE, (term, key_, value))

    array._term = term  # type: ignore
    return constraint


def compact_helper(
    solver: Solver, constraint: Constraint, term: Uint[N], concrete: Uint[N]
) -> tuple[Constraint, Uint[N]]:
    """Select between original and concretized versions of a term."""
    extended = constraint & (term == concrete)
    if solver.check(~extended):
        return constraint, term
    else:
        return extended, concrete


@overload
def evaluate(solver: Solver, s: Constraint) -> bool:
    ...


@overload
def evaluate(solver: Solver, s: Array[K, V]) -> dict[int, int]:
    ...


def evaluate(solver: Solver, s: Constraint | Array[K, V]) -> bool | dict[int, int]:
    """Backdoor method for evaluating non-bitvectors."""
    if not solver._current or _bitwuzla.last_check is not solver:  # type: ignore
        raise ValueError("solver is not ready for model evaluation.")

    match s:
        case Constraint():
            return s._evaluate()  # type: ignore
        case Array():
            return dict(
                (int(k, 2), int(v, 2))
                for k, v in BZLA.get_value_str(s._term).items()  # type: ignore
            )


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

    def __init__(self, key: bytes) -> None:
        """Create a new NarrowingError."""
        self.key = key

    def __str__(self) -> str:
        return self.key.hex()


class Array(zArray[K, V]):
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

    @classmethod
    def equals(cls, left: Array[K, V], right: Array[K, V]) -> Constraint:
        """Compare the two arrays for equality."""
        return _from_expr(Constraint, Kind.EQUAL, left, right)

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
