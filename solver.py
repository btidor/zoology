"""Interface to the SMT solver."""

from __future__ import annotations

from typing import Any, List, Literal, Optional, TypeVar, overload

from pysmt import logics
from pysmt.shortcuts import get_env, get_model

from smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)

get_env().factory.add_generic_solver("cvc5", "cvc5", [logics.QF_AUFBV])


class Solver:
    """An interface to the pySMT library."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraints: List[Constraint] = []
        self.model: Optional[Any] = None

    def assert_and_track(self, constraint: Constraint) -> None:
        """Track a new constraint."""
        self.model = None
        self.constraints.append(constraint)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        formulas = self.constraints + list(assumptions)
        self.model = get_model(Constraint.all(*formulas).node)
        return self.model is not None

    @overload
    def evaluate(self, value: T, model_completion: Literal[True]) -> T:
        ...

    @overload
    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        ...

    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        """Evaluate a given bitvector expression with the given model."""
        assert self.model is not None
        if value.node.is_constant():
            if (result := value.node.constant_value()) is None:
                return None
        else:
            result = self.model.get_value(value.node, model_completion)
            if not result.is_constant():
                assert model_completion is False
                return None
            result = result.constant_value()
        return value.__class__(result) if value is not None else None
