"""Interface to the SMT solver."""

from __future__ import annotations

import io
from typing import Dict, List, Literal, Optional, Tuple, TypeVar, overload

import z3
from pysmt import logics
from pysmt.fnode import FNode
from pysmt.shortcuts import Portfolio, get_env
from pysmt.smtlib.parser import get_formula
from pysmt.solvers.portfolio import Portfolio as PortfolioType
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
        self.cached_solver: Optional[PortfolioType] = None
        self.model: Optional[Dict[str, Tuple[z3.ExprRef, z3.ExprRef]]] = None

    def assert_and_track(self, constraint: Constraint) -> None:
        """Track a new constraint."""
        self.cached_solver, self.model = None, None
        self.constraints.append(constraint)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        # Bitwuzla is very fast, but can't solve all situations
        solver = Portfolio(["bitwuzla", "msat"], logics.QF_ABV)
        for constraint in self.constraints + list(assumptions):
            # FYI, this Z3 -> pySMT conversion process only works for boolean
            # constraints, not arbitrary expressions ¯\_(ツ)_/¯
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
            solver.add_assertion(fnode)

        if solver.solve():
            self.cached_solver = solver
            self.model = None
            return True
        else:
            self.cached_solver = None
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
        assert self.cached_solver is not None

        if value.is_constant_literal():
            return value

        if self.model is None:
            self.model = {}
            for key, val in self.cached_solver.get_model().assignment.items():
                symbol = translate_pysmt_symbol(key)
                constant = translate_pysmt_constant(val)
                self.model[symbol.decl().name()] = (symbol, constant)

        for symbol in get_vars(value.node):
            name = symbol.decl().name()
            if name in self.model:
                continue

            if model_completion:
                self.model[name] = (symbol, zero_for_z3_sort(symbol.sort()))
            else:
                return None

        expr = z3.substitute(value.node, list(self.model.values()))
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


def translate_pysmt_symbol(node: FNode) -> z3.ExprRef:
    """Convert a pySMT symbol into a Z3 expression."""
    assert node.is_symbol(), f"expected symbol, got {node}"
    sname, stype = node.symbol_name(), node.symbol_type()

    if stype.is_bool_type():
        return z3.Bool(sname)
    elif stype.is_bv_type():
        return z3.BitVec(sname, stype.width)
    elif stype.is_array_type():
        assert stype.index_type.is_bv_type()
        assert stype.elem_type.is_bv_type()
        return z3.Array(
            sname,
            z3.BitVecSort(stype.index_type.width),
            z3.BitVecSort(stype.elem_type.width),
        )
    else:
        raise TypeError(f"unhandled type: {stype}")


def translate_pysmt_constant(node: FNode) -> z3.ExprRef:
    """Convert a pySMT constant into a Z3 expression."""
    if node.is_constant():
        ctype, cvalue = node.constant_type(), node.constant_value()
        if ctype.is_bool_type():
            return z3.BoolVal(cvalue)
        elif ctype.is_bv_type():
            return z3.BitVecVal(cvalue, node.bv_width())
        else:
            raise TypeError(f"unhandled type: {ctype}")
    elif node.is_array_op():
        writes: Dict[int, int] = {}
        while node.is_store():
            node, i, x = node.args()
            if i in writes:
                continue  # last (outermost) write wins
            writes[i.bv_unsigned_value()] = x.bv_unsigned_value()
        assert node.is_array_value()

        domain = node.array_value_index_type()
        default = node.array_value_default()
        array = z3.K(
            z3.BitVecSort(domain.width),
            z3.BitVecVal(default.bv_unsigned_value(), default.bv_width()),
        )
        for i, x in writes.items():
            array = z3.Store(
                array,
                z3.BitVecVal(i, domain.width),
                z3.BitVecVal(x, default.bv_width()),
            )
        return array
    else:
        raise TypeError(f"expected constant or array, got {node}")


def zero_for_z3_sort(sort: z3.SortRef) -> z3.ExprRef:
    """Create the zero-valued expression for a given Z3 sort."""
    if sort.kind() == z3.Z3_BOOL_SORT:
        return z3.BoolVal(False)
    elif sort.kind() == z3.Z3_BV_SORT:
        assert isinstance(sort, z3.BitVecSortRef)
        return z3.BitVecVal(0, sort.size())
    elif sort.kind() == z3.Z3_ARRAY_SORT:
        assert isinstance(sort, z3.ArraySortRef)
        return z3.K(sort.domain(), zero_for_z3_sort(sort.range()))
    else:
        raise TypeError(f"unhandled z3 sort: {sort}")
