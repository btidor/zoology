"""Interfaces to SMT-solving backends."""

from __future__ import annotations

import abc
import subprocess
from typing import List, Literal, Optional, Set, cast, overload

import z3
from z3 import z3util

from symbolic import Constraint, is_bitvector


class Solver(abc.ABC):
    """A generic interface to the SMT solver."""

    @abc.abstractmethod
    def assert_and_track(self, constraint: Constraint, name: str) -> None:
        """Track a new constraint."""
        ...

    @abc.abstractmethod
    def minimize(self, objective: Constraint) -> None:
        """Add a new minimiziation objective."""
        ...

    @abc.abstractmethod
    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        ...

    @overload
    @abc.abstractmethod
    def evaluate(
        self, value: z3.BitVecRef, model_completion: Literal[True]
    ) -> z3.BitVecRef:
        ...

    @overload
    @abc.abstractmethod
    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        ...

    @abc.abstractmethod
    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        """Evaluate a given bitvector expression with the given model."""
        ...


class Z3PySolver(Solver):
    """An in-process instance of the Z3 solver."""

    def __init__(self) -> None:
        """Create a new Z3PySolver."""
        self.solver = z3.Optimize()
        self.model: Optional[z3.ModelRef] = None

    def assert_and_track(self, constraint: Constraint, name: str) -> None:
        """Track a new constraint."""
        self.model = None
        self.solver.assert_and_track(constraint, name)

    def minimize(self, objective: Constraint) -> None:
        """Add a new minimiziation objective."""
        self.model = None
        self.solver.minimize(objective)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        result = self.solver.check(*assumptions)
        if result == z3.sat:
            self.model = self.solver.model()
            return True
        elif result == z3.unsat:
            return False
        else:
            raise Exception(f"z3py error: {self.solver.reason_unknown()}")

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: Literal[True]
    ) -> z3.BitVecRef:
        ...

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        ...

    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        """Evaluate a given bitvector expression with the given model."""
        assert self.model is not None
        return cast(
            Optional[z3.BitVecRef],
            self.model.evaluate(value, model_completion),
        )


class Z3BinSolver(Solver):
    """An out-of-process instance of the Z3 solver."""

    def __init__(self) -> None:
        """Create a new Z3BinSolver."""
        self.objectives: List[Constraint] = []
        self.proc: subprocess.Popen[str] = subprocess.Popen(
            ["z3", "-in"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        self.state = 0
        self.vars: Set[str] = set()
        self.extra: Set[str] = set()

    def assert_and_track(self, constraint: Constraint, name: str) -> None:
        """Track a new constraint."""
        self._reset()
        self._write("assert", constraint)

    def minimize(self, objective: Constraint) -> None:
        """Add a new minimiziation objective."""
        self._reset()
        self._write("minimize", objective)

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None

        self._reset()

        if len(assumptions) > 0:
            self.proc.stdin.write(f"(push 1)\n")
            for assumption in assumptions:
                self._write("assert", assumption, True)

        self.proc.stdin.write(f"(check-sat)\n")
        self.proc.stdin.flush()

        result = self.proc.stdout.readline().strip()
        if result == "sat":
            self.state = 1 if len(assumptions) == 0 else 2
            return True
        elif result == "unsat":
            if len(assumptions) > 0:
                self.proc.stdin.write(f"(pop 1)\n")
            return False
        else:
            raise Exception(f"z3 failure: {result}")

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: Literal[True]
    ) -> z3.BitVecRef:
        ...

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        ...

    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        """Evaluate a given bitvector expression with the given model."""
        if not is_bitvector(value):
            raise ValueError("unexpected non-bitvector")

        assert self.state > 0
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None

        for var in z3util.get_vars(value):
            name = var.decl().name()
            if name in self.vars:
                continue
            self.vars.add(name)
            self.proc.stdin.write(var.decl().sexpr())

        self.proc.stdin.write(
            f"(eval {value.sexpr()} :completion {str(model_completion).lower()})\n"
        )
        self.proc.stdin.flush()

        result = self.proc.stdout.readline().strip()
        if result.startswith("#x"):
            b = bytes.fromhex(result[2:])
            return z3.BitVecVal(int.from_bytes(b, "big"), len(b) * 8)
        elif result.startswith("(error "):
            raise Exception(f"z3 error: {result}")
        else:
            assert model_completion is False
            return None

    def _write(self, key: str, constraint: Constraint, extra: bool = False) -> None:
        assert self.proc.stdin is not None

        if constraint is True or constraint is False:
            sexpr = str(constraint).lower()
        else:
            sexpr = constraint.sexpr()

        for var in z3util.get_vars(constraint):
            name = var.decl().name()
            if name in self.vars or name in self.extra:
                continue
            if extra:
                self.extra.add(name)
            else:
                self.vars.add(name)
            self.proc.stdin.write(var.decl().sexpr())

        self.proc.stdin.write(f"({key} {sexpr})\n")

    def _reset(self) -> None:
        assert self.proc.stdin is not None
        if self.state == 2:
            self.proc.stdin.write(f"(pop 1)\n")
        self.state = 0
        self.extra = set()


class CVC5Solver(Solver):
    """An out-of-process instance of the CVC5 solver."""

    def __init__(self) -> None:
        """Create a new CVC5Solver."""
        self.objectives: List[Constraint] = []
        self.proc: subprocess.Popen[str] = subprocess.Popen(
            ["cvc5", "--incremental"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        assert self.proc.stdin is not None
        self.proc.stdin.write(f"(set-logic QF_ABV)\n")
        self.state = 0
        self.vars: Set[str] = set()
        self.extra: Set[str] = set()

    def assert_and_track(self, constraint: Constraint, name: str) -> None:
        """Track a new constraint."""
        self._reset()
        self._write("assert", constraint)

    def minimize(self, objective: Constraint) -> None:
        """Add a new minimiziation objective."""
        pass  # not supported

    def check(self, *assumptions: Constraint) -> bool:
        """
        Check whether the given solver state is satisfiable.

        Returns a model (if sat) or None (if unsat). Raises an error if the
        solver fails.
        """
        assert self.proc.stdin is not None
        assert self.proc.stdout is not None

        self._reset()

        if len(assumptions) > 0:
            self.proc.stdin.write(f"(push 1)\n")
            for assumption in assumptions:
                self._write("assert", assumption, True)

        self.proc.stdin.write(f"(check-sat)\n")
        self.proc.stdin.flush()

        result = self.proc.stdout.readline().strip()
        if result == "sat":
            self.state = 1 if len(assumptions) == 0 else 2
            return True
        elif result == "unsat":
            if len(assumptions) > 0:
                self.proc.stdin.write(f"(pop 1)\n")
            return False
        else:
            raise Exception(f"cvc5 failure: {result}")

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: Literal[True]
    ) -> z3.BitVecRef:
        ...

    @overload
    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        ...

    def evaluate(
        self, value: z3.BitVecRef, model_completion: bool = False
    ) -> Optional[z3.BitVecRef]:
        """Evaluate a given bitvector expression with the given model."""
        raise NotImplementedError

    def _write(self, key: str, constraint: Constraint, extra: bool = False) -> None:
        assert self.proc.stdin is not None

        if constraint is True or constraint is False:
            sexpr = str(constraint).lower()
        else:
            sexpr = constraint.sexpr()

        for var in z3util.get_vars(constraint):
            name = var.decl().name()
            if name in self.vars or name in self.extra:
                continue
            if extra:
                self.extra.add(name)
            else:
                self.vars.add(name)
            self.proc.stdin.write(var.decl().sexpr())

        self.proc.stdin.write(f"({key} {sexpr})\n")

    def _reset(self) -> None:
        assert self.proc.stdin is not None
        if self.state == 2:
            self.proc.stdin.write(f"(pop 1)\n")
        self.state = 0
        self.extra = set()


DefaultSolver = Z3PySolver
