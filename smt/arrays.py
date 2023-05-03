"""Types for representing symbolic arrays of bitvectors."""

from __future__ import annotations

import copy
from typing import Any, Generic, Iterable, Type, TypeVar

from pybitwuzla import BitwuzlaTerm, Kind

from .bitwuzla import mk_array_sort, mk_const, mk_const_array, mk_term
from .smt import BitVector
from .solver import Solver

K = TypeVar("K", bound=BitVector)
V = TypeVar("V", bound=BitVector)


class Array(Generic[K, V]):
    """
    A symbolic array. Mutable.

    Tracks which keys are accessed and written.
    """

    def __init__(self, array: BitwuzlaTerm, vtype: Type[V]) -> None:
        """Create a new Array. For internal use."""
        self.array = array
        self.vtype = vtype
        self.accessed: list[K] = []
        self.written: list[K] = []

    def __deepcopy__(self, memo: Any) -> Array[K, V]:
        result: Array[K, V] = Array(self.array, self.vtype)
        result.accessed = copy.deepcopy(self.accessed, memo)
        result.written = copy.deepcopy(self.written, memo)
        return result

    @classmethod
    def concrete(cls, key: Type[K], val: V) -> Array[K, V]:
        """Create a new Array with a concrete default value."""
        return Array(
            mk_const_array(mk_array_sort(key._sort(), val._sort()), val.node),
            val.__class__,
        )

    @classmethod
    def symbolic(cls, name: str, key: Type[K], val: Type[V]) -> Array[K, V]:
        """Create a new Array as an uninterpreted function."""
        return Array(mk_const(mk_array_sort(key._sort(), val._sort()), name), val)

    def __getitem__(self, key: K) -> V:
        """Look up the given symbolic key."""
        self.accessed.append(key)
        return self.peek(key)

    def __setitem__(self, key: K, val: V) -> None:
        """Set the given symbolic key to the given symbolic value."""
        self.written.append(key)
        self.poke(key, val)

    def peek(self, key: K) -> V:
        """Look up the given symbolic key, but don't track the lookup."""
        return self.vtype(mk_term(Kind.ARRAY_SELECT, [self.array, key.node]))

    def poke(self, key: K, val: V) -> None:
        """Set up the given symbolic key, but don't track the write."""
        self.array = mk_term(Kind.ARRAY_STORE, [self.array, key.node, val.node])

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
                k = solver.evaluate(key).describe()
                v = solver.evaluate(value).describe()
                p = solver.evaluate(prior).describe() if prior is not None else None
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
