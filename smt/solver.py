"""Interface to the SMT solver."""

from __future__ import annotations

from typing import Literal, TypeVar, overload

from pybitwuzla import Result

from .bitwuzla import assume_formula, check_sat, get_value
from .smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)


class Solver:
    """An interface to the Bitwuzla SMT solver."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraints: list[Constraint] = []
        self.solved = False

    def assert_and_track(self, constraint: Constraint) -> None:
        """Track a new constraint."""
        self.solved = False
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
            self.solved = True
            return True
        elif result == Result.UNSAT:
            self.solved = False
            return False
        else:
            raise ValueError("solver returned unknown")

    def unsat_core(self, *assumptions: Constraint) -> list[Constraint]:
        """Extract an unsatisfiable core for debugging."""
        raise NotImplementedError

    @overload
    def evaluate(self, value: T, model_completion: Literal[True]) -> T:
        ...

    @overload
    def evaluate(self, value: T, model_completion: bool = False) -> T | None:
        ...

    def evaluate(self, value: T, model_completion: bool = False) -> T | None:
        """Evaluate a given bitvector expression with the given model."""
        assert self.solved
        return value.__class__(get_value(value.node))


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
