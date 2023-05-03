"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Iterable

from environment import Universe
from smt.sha3 import SHA3
from smt.smt import Constraint, Uint160
from smt.solver import ConstrainingError, NarrowingError, Solver
from state import State


class History:
    """Encapsulates a linear sequence of transactions."""

    def __init__(
        self, starting_universe: Universe, starting_sha3: SHA3, player: Uint160
    ) -> None:
        """Create a new History."""
        self.starting_universe = starting_universe
        self.starting_sha3 = starting_sha3
        self.player = player
        self.states: list[State] = []

    def subsequent(self) -> tuple[Universe, SHA3]:
        """Set up the execution of a new transaction."""
        if len(self.states) == 0:
            pair = (self.starting_universe, self.starting_sha3)
        else:
            pair = (self.states[-1].universe, self.states[-1].sha3)
        return copy.deepcopy(pair)

    def extend(self, state: State) -> History:
        """Add a new transaction to the History."""
        other = copy.deepcopy(self)
        other.states.append(state)
        return other

    def constrain(self, solver: Solver) -> None:
        """Apply hard constraints to the given solver instance."""
        for state in self.states:
            state.constrain(solver)
        if not solver.check():
            raise ConstrainingError

    def narrow(self, solver: Solver, skip_sha3: bool = False) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        if not skip_sha3:
            if len(self.states) > 0:
                self.states[-1].sha3.narrow(solver)
            else:
                self.starting_sha3.narrow(solver)

        for state in self.states:
            state.narrow(solver)

    def describe(
        self, *constraints: Constraint, skip_final: bool = False
    ) -> Iterable[str]:
        """Yield a human-readable description of the transaction sequence."""
        solver = Solver()
        for constraint in constraints:
            solver.assert_and_track(constraint)
        try:
            self.constrain(solver)
        except ConstrainingError:
            yield "unprintable: unsatisfiable"
            return

        try:
            self.narrow(solver)
        except NarrowingError:
            yield "unprintable: narrowing error"
            solver = Solver()
            for constraint in constraints:
                solver.assert_and_track(constraint)
            self.constrain(solver)
            self.narrow(solver, skip_sha3=True)

        states = self.states
        if skip_final:
            states = states[:-1]
        for state in states:
            data = state.transaction.calldata.describe(solver)
            if len(data) == 0:
                data = "(empty) "
            elif len(data) > 8:
                data = data[:8] + " " + data[8:]
            line = f"{state.px()}\t{data}"

            suffixes = []
            value = solver.evaluate(state.transaction.callvalue).unwrap()
            if value > 0:
                suffixes.append(f"value: {value}")
            caller = solver.evaluate(state.transaction.caller)
            if (caller != self.player).unwrap():
                suffixes.append(f"via proxy")
            if len(suffixes) > 0:
                line += f"\t({', '.join(suffixes)})"

            yield line
