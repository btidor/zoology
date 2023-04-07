"""Interface to the SMT solver."""

from __future__ import annotations

from typing import List, Literal, Optional, TypeVar, overload

import z3

from smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)


class Solver:
    """An interface to the Z3 library."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.model: Optional[z3.ModelRef] = None
        self.solver = z3.Solver()

    def assert_and_track(self, constraint: Constraint) -> None:
        """Track a new constraint."""
        self.model = None
        self.solver.add(constraint.node)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        result = self.solver.check(*[c.node for c in assumptions])
        if result == z3.sat:
            self.model = self.solver.model()
            return True
        elif result == z3.unsat:
            return False
        else:
            raise Exception(f"z3 error: {self.solver.reason_unknown()}")

    def unsat_core(self, *assumptions: Constraint) -> List[Constraint]:
        """Extract an unsatisfiable core for debugging."""
        assert self.check(*assumptions) is False
        constraints = []
        for item in self.solver.unsat_core():
            assert isinstance(item, z3.BoolRef)
            constraints.append(Constraint(item))
        return constraints

    @overload
    def evaluate(self, value: T, model_completion: Literal[True]) -> T:
        ...

    @overload
    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        ...

    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        """Evaluate a given bitvector expression with the given model."""
        assert self.model is not None
        ref = self.model.evaluate(value.node, model_completion)
        assert isinstance(ref, z3.BitVecRef)
        return value.__class__(ref)


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
