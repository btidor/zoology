"""Interface to the SMT solver."""

from __future__ import annotations

from typing import Dict, List, Literal, Optional, TypeVar, overload

from pysmt import logics
from pysmt.fnode import FNode
from pysmt.shortcuts import BV, Array, Bool, Portfolio, get_env

from smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)


get_env().factory.add_generic_solver("cvc5", "cvc5", [logics.QF_AUFBV])
get_env().factory.add_generic_solver("bitwuzla", "bitwuzla", [logics.QF_AUFBV])


class Solver:
    """An interface to the pySMT library."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraints: List[Constraint] = []
        self.model: Optional[Dict[FNode, FNode]] = None

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
                self.model = s.get_model().assignment
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

        for var in value.node.get_free_variables():
            if var in self.model:
                continue

            if model_completion is False:
                return None

            # Model Completion (adapted from pysmt:solvers/eager.py)
            assert var.is_symbol(), f"expected symbol, got {var}"
            sym = var.symbol_type()
            if sym.is_bool_type():
                self.model[var] = Bool(False)
            elif sym.is_bv_type():
                self.model[var] = BV(0, var.bv_width())
            elif sym.is_array_type():
                self.model[var] = Array(sym.index_type, BV(0, sym.elem_type.width))
            else:
                raise TypeError(f"unhandled type: {var.symbol_type()}")

        result = value.__class__(value.node.substitute(self.model).simplify())
        assert result.node.is_constant()
        return result


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
