"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Any, Iterable

from environment import Block
from smt import (
    ConstrainingError,
    Solver,
    Uint160,
)
from state import State


class Sequence:
    """Represents a linear sequence of synthetic transactions."""

    factory: Uint160
    instance: Uint160
    player: Uint160
    proxy: Uint160
    blocks: list[Block]

    # The first state is the concrete createInstance(...) call, followed by the
    # synthetic transactions.
    states: list[State]

    def __init__(
        self,
        factory: Uint160,
        instance: Uint160,
        player: Uint160,
        proxy: Uint160,
        start: State,
    ) -> None:
        """Create a new Sequence."""
        self.factory = factory
        self.instance = instance
        self.player = player
        self.proxy = proxy

        # The ith transaction in `state` runs in the ith block. Validation
        # always runs in the last block.
        block = start.block
        self.blocks = list[Block]()
        for _ in range(16):
            block = block.successor()
            self.blocks.append(block)

        self.states = list[State]([start])

    def __deepcopy__(self, memo: Any) -> Sequence:
        result = copy.copy(self)
        result.states = copy.copy(result.states)
        return result

    def pz(self) -> str:
        """Return a human-readable version of the sequence of paths."""
        return "Pz" + ":".join(map(lambda s: s.px()[2:], self.states))

    def extend(self, state: State) -> Sequence:
        """Add a new transaction to the Sequence."""
        result = copy.deepcopy(self)
        result.states.append(state)
        if len(result.states) > 16:
            raise OverflowError("sequence is limited to 15 states")
        return result

    def constrain(self, solver: Solver, check: bool = True) -> None:
        """Apply hard constraints to the given solver instance."""
        solver.add(self.states[-1].constraint)
        if check and not solver.check():
            raise ConstrainingError

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        for state in self.states:
            state.narrow(solver)
        self.states[-1].sha3.narrow(solver)
        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the Sequence."""
        assert (codesize := self.states[-1].mystery_size) is not None
        if (sz := solver.evaluate(codesize)) != 0x123:
            yield f"Proxy CODESIZE {hex(sz)}{' (via constructor)' if sz == 0 else ''}\n"

        for state in self.states[1:]:
            if (state.transaction.address == self.instance).reveal() is not True:
                assert (addr := state.transaction.address.reveal()) is not None
                yield f"To 0x{addr.to_bytes(20).hex()}:\n    "

            if isinstance(state.pc, int):  # SELFDESTRUCT balance transfer
                value = solver.evaluate(state.transaction.callvalue)
                yield f"SELFDESTRUCT\tvalue: {value}\n"
                continue

            yield from state.transaction.calldata.describe(solver)

            value = solver.evaluate(state.transaction.callvalue)
            if value > 0:
                yield f"\tvalue: {value}"
            caller = solver.evaluate(state.transaction.caller)
            player = solver.evaluate(self.player)
            if caller != player:
                yield "\tvia proxy"
            yield "\n"
            assert state.mystery_proxy is not None

            for call in state.calls:
                yield from call.describe(solver, state.mystery_proxy)
