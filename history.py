"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Any, Iterable

from environment import Block, Universe
from sha3 import SHA3
from smt import (
    ConstrainingError,
    Constraint,
    Expression,
    Solver,
    Uint160,
    Uint256,
    get_constants,
    substitute,
)
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

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        if len(self.states) > 0:
            self.states[-1].sha3.narrow(solver)
        else:
            self.starting_sha3.narrow(solver)

        for state in self.states:
            state.narrow(solver)

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the transaction sequence."""
        for state in self.states:
            data = state.transaction.calldata.describe(solver)
            if len(data) == 0:
                data = "(empty) "
            elif len(data) > 8:
                data = data[:8] + " " + data[8:]
            line = f"{state.px()}\t{data}"

            suffixes: list[str] = []
            value = solver.evaluate(state.transaction.callvalue)
            if value > 0:
                suffixes.append(f"value: {value}")
            caller = solver.evaluate(state.transaction.caller)
            player = solver.evaluate(self.player)
            if caller != player:
                suffixes.append(f"via proxy")
            if len(suffixes) > 0:
                line += f"\t({', '.join(suffixes)})"

            yield line


class Validator:
    """Represents the result of running validateInstance."""

    def __init__(self, constraint: Constraint) -> None:
        """Create a new Validator."""
        self.constraint = constraint
        self._constants = get_constants(constraint)
        for name in self._constants.keys():
            if name.startswith("STORAGE@"):
                continue
            elif name == "BALANCE":
                continue
            elif name == "NUMBER":
                continue
            raise ValueError(f"validator depends on unsupported variable: {name}")

    def translate(self, history: History) -> Constraint:
        """Translate the validation constraint onto the given History."""
        if len(history.states) == 0:
            universe = history.starting_universe
            number = Uint256(0)
        else:
            universe = history.states[-1].universe
            number = history.states[-1].block.number + Uint256(1)

        substitutions: dict[Any, Expression] = {}
        for name, term in self._constants.items():
            if name.startswith("STORAGE@"):
                addr = int(name[8:], 16)
                substitutions[term] = universe.contracts[addr].storage
            elif name == "BALANCE":
                substitutions[term] = universe.balances
            elif name == "NUMBER":
                substitutions[term] = number
            else:
                raise ValueError(f"unknown variable: {name}")

        return substitute(self.constraint, substitutions)
