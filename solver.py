"""Interface to the SMT solver."""

from __future__ import annotations

import io
from typing import Dict, List, Literal, Optional, Tuple, TypeVar, overload

import z3
from pysmt import logics
from pysmt.shortcuts import Portfolio, get_env
from pysmt.smtlib.parser import get_formula
from z3.z3util import get_vars

from smt import BitVector, Constraint

T = TypeVar("T", bound=BitVector)

get_env().factory.add_generic_solver("cvc5", "cvc5", [logics.QF_AUFBV])
get_env().factory.add_generic_solver("bitwuzla", "bitwuzla", [logics.QF_AUFBV])


class Solver:
    """An interface to the Z3 and pySMT solvers."""

    def __init__(self) -> None:
        """Create a new Solver."""
        self.constraints: List[Constraint] = []
        self.model: Optional[Dict[str, Tuple[z3.ExprRef, z3.ExprRef]]] = None

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
            for constraint in self.constraints + list(assumptions):
                # FYI, this Z3 -> pySMT conversion process only works for
                # boolean constraints, not arbitrary expressions ¯\_(ツ)_/¯
                smtlib = z3.Z3_benchmark_to_smtlib_string(
                    constraint.node.ctx_ref(),
                    None,
                    None,
                    None,
                    None,
                    0,
                    None,
                    constraint.node.as_ast(),
                )
                fnode = get_formula(io.StringIO(smtlib))
                s.add_assertion(fnode)

            if s.solve():
                self.model = {}
                for key, val in s.get_model().assignment.items():
                    assert key.is_symbol(), f"expected symbol, got {key}"
                    name, sym = key.symbol_name(), key.symbol_type()
                    if sym.is_bool_type():
                        if val.is_true():
                            self.model[name] = (z3.Bool(name), z3.BoolVal(True))
                        elif val.is_false():
                            self.model[name] = (z3.Bool(name), z3.BoolVal(False))
                        else:
                            raise TypeError("bool is neither true nor false")
                    elif sym.is_bv_type():
                        self.model[name] = (
                            z3.BitVec(name, val.bv_width()),
                            z3.BitVecVal(val.bv_unsigned_value(), val.bv_width()),
                        )
                    elif sym.is_array_type():
                        raise NotImplementedError
                    else:
                        raise TypeError(f"unhandled type: {sym}")
                return True
            else:
                self.model = None
                return False

    def unsat_core(self, *assumptions: Constraint) -> List[Constraint]:
        """Extract an unsatisfiable core for debugging."""
        solver = z3.Solver()
        for constraint in self.constraints:
            solver.add(constraint.node)
        for assumption in assumptions:
            solver.add(assumption.node)
        assert solver.check() == z3.unsat

        core = []
        for item in solver.unsat_core():
            assert isinstance(item, z3.BoolRef)
            core.append(Constraint(item))
        return core

    @overload
    def evaluate(self, value: T, model_completion: Literal[True]) -> T:
        ...

    @overload
    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        ...

    def evaluate(self, value: T, model_completion: bool = False) -> Optional[T]:
        """Evaluate a given bitvector expression with the given model."""
        assert self.model is not None

        if value.is_constant_literal():
            return value

        for var in get_vars(value.node):
            if (name := var.decl().name()) in self.model:
                pass
            elif model_completion is False:
                return None
            else:
                # TODO: detect type and insert zero value
                raise NotImplementedError

        print(value.node, self.model.values())
        expr = z3.substitute(value.node, self.model.values())
        expr = z3.simplify(expr)
        assert isinstance(expr, z3.BitVecRef)

        result = value.__class__(expr)
        assert result.is_constant_literal()
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
