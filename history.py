"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Any, Iterable

from environment import Block, Universe
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

    def __deepcopy__(self, memo: Any) -> History:
        result = History(self.starting_universe, self.starting_sha3, self.player)
        result.states = copy.copy(self.states)
        return result

    def pxs(self) -> str:
        """Return a human-readable version of the sequence of paths."""
        return ":".join(map(lambda s: s.px(), self.states))

    def subsequent(self) -> tuple[Universe, SHA3, Block]:
        """Set up the execution of a new transaction."""
        if len(self.states) == 0:
            universe = self.starting_universe
            sha3 = self.starting_sha3
            block = Block()
        else:
            universe = self.states[-1].universe
            sha3 = self.states[-1].sha3
            block = self.states[-1].block.successor()
        return copy.deepcopy(universe), copy.deepcopy(sha3), block

    def extend(self, state: State) -> History:
        """Add a new transaction to the History."""
        other = copy.deepcopy(self)
        other.states.append(state)
        return other

    def constrain(self, solver: Solver, check: bool = True) -> None:
        """Apply hard constraints to the given solver instance."""
        for state in self.states:
            state.constrain(solver)
        if check and not solver.check():
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
            yield f"[{self.pxs()}] unprintable: unsatisfiable"
            return

        try:
            self.narrow(solver)
        except NarrowingError:
            yield f"[{self.pxs()}] unprintable: narrowing error"
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

            suffixes: list[str] = []
            value = solver.evaluate(state.transaction.callvalue).unwrap()
            if value > 0:
                suffixes.append(f"value: {value}")
            caller = solver.evaluate(state.transaction.caller)
            if (caller != self.player).unwrap():
                suffixes.append(f"via proxy")
            if len(suffixes) > 0:
                line += f"\t({', '.join(suffixes)})"

            yield line
