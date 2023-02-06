"""Interface to the SMT solver."""

from __future__ import annotations

import warnings
from typing import Any, List, Literal, Optional, TypeVar, overload

from pysmt import logics
from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import Portfolio, get_env

from smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)


get_env().factory.add_generic_solver("cvc5", "cvc5", [logics.QF_AUFBV])
get_env().factory.add_generic_solver("bitwuzla", "bitwuzla", [logics.QF_AUFBV])


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
        # Bitwuzla is very fast, but can't solve all situations
        with Portfolio(["bitwuzla", "msat"], logics.QF_ABV) as s:
            s.add_assertions(c.node for c in self.constraints)
            s.add_assertions(c.node for c in assumptions)
            if s.solve():
                self.model = s.get_model()
                return True
            return False

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
            try:
                result = self.model.get_value(value.node, model_completion)
            except PysmtTypeError:
                result = None
            if result is None or not result.is_constant():
                if model_completion is False:
                    return None
                else:
                    warnings.warn("filling in invalid evaluation result")
                    return value.__class__(0)
            result = result.constant_value()
        return value.__class__(result) if value is not None else None
