"""Interface to the SMT solver."""

from __future__ import annotations

from typing import Type, overload

from pybitwuzla import Result

from .bitwuzla import assume_formula, check_sat, get_unsat_assumptions, get_value_int
from .smt import BitVector, Constraint


class Solver:
    """An interface to the Bitwuzla SMT solver."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraints: list[Constraint] = []
        self.latest_result: bool | None = None

    def assert_and_track(self, constraint: Constraint) -> None:
        """Track a new constraint."""
        self.latest_result = None
        self.constraints.append(constraint)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        assume_formula(*(c.node for c in self.constraints))
        assume_formula(*(c.node for c in assumptions))

        result = check_sat()
        if result == Result.SAT:
            self.latest_result = True
            return True
        elif result == Result.UNSAT:
            self.latest_result = False
            return False
        else:
            raise ValueError("solver returned unknown")

    def unsat_core(self) -> list[Constraint]:
        """Extract an unsatisfiable core for debugging."""
        assert self.latest_result is False
        core: list[Constraint] = []
        for term in get_unsat_assumptions():
            core.append(Constraint(term))
        return core

    @overload
    def evaluate(self, value: BitVector, into: Type[int] = int) -> int:
        ...

    @overload
    def evaluate(self, value: BitVector, into: Type[bytes]) -> bytes:
        ...

    def evaluate(
        self, value: BitVector, into: Type[int] | Type[bytes] = int
    ) -> int | bytes:
        """Evaluate a given bitvector expression with the given model."""
        assert self.latest_result is True

        v = get_value_int(value.node)
        if into == int:
            return v
        elif into == bytes:
            return v.to_bytes(value.length() // 8)
        else:
            raise TypeError(f"unknown into type: {into}")


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
