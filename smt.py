"""A library of augmentations for zbitvector."""

from __future__ import annotations

import copy
from typing import Any, Iterable, Literal, Self, TypeVar, Union

from Crypto.Hash import keccak
from zbitvector import Array as zArray
from zbitvector import Constraint, Int, Solver, Symbolic, Uint
from zbitvector._bitwuzla import BZLA, BitwuzlaTerm, Kind

Uint8 = Uint[Literal[8]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]

_Uint257 = Uint[Literal[257]]


def make_uint(n: int) -> type[Uint[Any]]:
    """Create a new UintN class from a given N."""
    return Uint[Literal[n]]  # type: ignore


def concat_bytes(*args: Uint8) -> Uint[Any]:
    """Concatenate a series of Uint8s into a longer UintN."""
    return Uint[Literal[len(args) * 8]]._from_expr(Kind.BV_CONCAT, *args)  # type: ignore


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    """Return a constraint asserting that a + b does not overflow."""
    return ~Constraint._from_expr(Kind.BV_UADD_OVERFLOW, a, b)  # type: ignore


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    """Return a constraint asserting that a - b does not underflow."""
    return ~Constraint._from_expr(Kind.BV_USUB_OVERFLOW, a, b)  # type: ignore


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
        p: list[str] = []
        while v > 0:
            b = v & ((1 << 256) - 1)
            p.append(hex(b)[2:])
            v >>= 256
        return f"0x[{'.'.join(reversed(p))}]"
    else:
        digest = keccak.new(
            data=bv._term.dump("smt2").encode(), digest_bits=256  # type: ignore
        ).digest()
        return "#" + digest[:3].hex()


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


K = TypeVar("K", bound=Union[Uint[Any], Int[Any]])
V = TypeVar("V", bound=Union[Uint[Any], Int[Any]])


class Array(zArray[K, V]):
    """A wrapper around zbitvector.Array. Supports read and write tracking."""

    def __init__(self, value: V | str, /) -> None:
        """Create a new Array."""
        super().__init__(value)
        self.accessed: list[K] = []
        self.written: list[K] = []

    def __deepcopy__(self, memo: Any) -> Self:
        result = super().__deepcopy__(memo)
        result.accessed = copy.copy(self.accessed)
        result.written = copy.copy(self.written)
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
            concrete: dict[str, tuple[str, str | None]] = {}
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


S = TypeVar("S", bound=Symbolic)


def get_constants(s: Symbolic) -> dict[str, BitwuzlaTerm]:
    """Recursively search the term for constants."""
    constants: dict[str, BitwuzlaTerm] = {}
    queue: set[BitwuzlaTerm] = set([s._term])  # type: ignore
    while queue:
        item = queue.pop()
        queue.update(item.get_children())
        if item.is_const():
            assert (sym := item.get_symbol()) is not None
            constants[sym] = item
    return constants


def substitute(s: S, subst_map: dict[BitwuzlaTerm, Symbolic | Array[Any, Any]]) -> S:
    """Perform term substitution according to the given map."""
    if len(subst_map) == 0:
        return s
    result = s.__class__.__new__(s.__class__)
    result._term = BZLA.substitute(s._term, dict((k, v._term) for k, v in subst_map.items()))  # type: ignore
    return result
