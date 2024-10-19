"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Any, Iterable

from environment import Block
from smt import (
    Solver,
    Uint52,
    Uint160,
    Uint256,
)
from snapshot import PLAYER
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

    selfdestructs: list[dict[int, Uint256]]

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
        self.blocks = [start.block]
        for _ in range(1, 16):
            self.blocks.append(self.blocks[-1].successor())

        self.states = [start]
        self.selfdestructs = [_selfdestruct(start, 0)]

    def __deepcopy__(self, memo: Any) -> Sequence:
        result = copy.copy(self)
        result.states = copy.copy(result.states)
        result.selfdestructs = copy.copy(result.selfdestructs)
        return result

    def pz(self) -> str:
        """Return a human-readable version of the sequence of paths."""
        return "Pz" + ":".join(map(lambda s: s.px()[2:], self.states[1:]))

    def extend(self, state: State) -> Sequence:
        """Add a new transaction to the Sequence."""
        result = copy.deepcopy(self)
        result.states.append(state)
        result.selfdestructs.append(_selfdestruct(state, len(self.states)))
        if len(result.states) > 16:
            raise OverflowError("sequence is limited to 15 states")
        return result

    @property
    def solver(self) -> Solver:
        """Return a reference to the current (mutable!) solver."""
        return self.states[-1].solver

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        for i in range(9):
            constraint = self.states[0].mystery_size == Uint256(0x123 >> i)
            if solver.check(constraint):
                solver.add(constraint)
                break

        for i, (state, selfdestruct) in enumerate(zip(self.states, self.selfdestructs)):
            if i != 0:  # skip narrowing on createInstance(...) for speed
                state.narrow(solver)
            for value in selfdestruct.values():
                for i in range(257):
                    constraint = value == Uint256(2**i - 1)
                    if solver.check(constraint):
                        solver.add(constraint)
                        break
            assert solver.check()

        self.states[-1].sha3.narrow(solver)
        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the Sequence."""
        assert (codesize := self.states[-1].mystery_size) is not None
        if (sz := solver.evaluate(codesize)) != 0x123:
            yield f"Proxy CODESIZE {hex(sz)}{' (via constructor)' if sz == 0 else ''}\n"

        for i, (state, selfdestruct) in enumerate(zip(self.states, self.selfdestructs)):
            if i != 0:
                # Transaction
                if (state.transaction.address == self.instance).reveal() is not True:
                    assert (addr := state.transaction.address.reveal()) is not None
                    yield f"To 0x{addr.to_bytes(20).hex()}:\n    "

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

            # Post-transaction SELFDESTRUCT
            for address, symbolic in selfdestruct.items():
                if (value := solver.evaluate(symbolic)) == 0:
                    continue
                if address != self.instance.reveal():
                    yield f"To 0x{address.to_bytes(20).hex()}:\n    "
                yield f"SELFDESTRUCT\tvalue: {value}\n"


def _selfdestruct(state: State, i: int) -> dict[int, Uint256]:
    """
    Mutate this state, simulating a SELFDESTRUCT to each contract.

    Pure transfers of value are represented by a SELFDESTRUCT. This is more
    general than a `receive()` method because it always succeeds.
    """
    deltas = dict[int, Uint256]()
    for address, contract in state.contracts.items():
        if contract.invisible:
            continue
        d = Uint52(f"SELFDESTRUCT@{address.to_bytes(20).hex()}-{i}").into(Uint256)
        state.balances[PLAYER] -= d
        state.balances[Uint160(address)] += d
        deltas[address] = d
    return deltas
