"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from typing import Any, Iterable

from environment import Block, Contract
from sha3 import SHA3
from smt import (
    Array,
    ConstrainingError,
    Constraint,
    Expression,
    Solver,
    Uint160,
    Uint256,
    evaluate,
    get_constants,
    substitute,
)
from state import Call, DelegateCall, GasHogCall, State


class History:
    """Encapsulates a linear sequence of transactions."""

    def __init__(
        self,
        contracts: dict[int, Contract],
        balances: Array[Uint160, Uint256],
        sha3: SHA3,
        player: Uint160,
    ) -> None:
        """Create a new History."""
        block = Block()
        self.player = player
        self.start = (contracts, balances, sha3, block)
        self.states = list[State]()
        self.final: State | None = None
        # The ith transaction in `state` runs in the ith block. Validation
        # always runs against the last block.
        self.blocks = list[Block]()
        for _ in range(16):
            block = block.successor()
            self.blocks.append(block)

    def __deepcopy__(self, memo: Any) -> History:
        result = copy.copy(self)
        result.states = copy.copy(result.states)
        return result

    def pz(self) -> str:
        """Return a human-readable version of the sequence of paths."""
        return "Pz" + ":".join(map(lambda s: s.px()[2:], self.states))

    def subsequent(
        self,
    ) -> tuple[dict[int, Contract], Array[Uint160, Uint256], SHA3, Block]:
        """Set up the execution of a new transaction."""
        if len(self.states) == 0:
            contracts, balances, sha3, block = self.start
        else:
            i = len(self.states) - 1
            contracts = self.states[i].contracts
            balances = self.states[i].balances
            sha3 = self.states[i].sha3
            block = self.blocks[i]
        return (
            {k: v.clone_and_reset() for (k, v) in contracts.items()},
            balances.clone_and_reset(),
            copy.deepcopy(sha3),
            block,
        )

    def validation_block(self) -> Block:
        """Return the block in which validateInstance should run."""
        return self.blocks[-1]

    def extend(self, state: State) -> History:
        """Add a new transaction to the History."""
        next = copy.deepcopy(self)
        next.states.append(state)
        if len(next.states) > 15:
            raise OverflowError("History is limited to 15 states")
        return next

    def with_final(self, final: State | None) -> History:
        """Add the final validateInstance transaction to the History."""
        assert self.final is None
        next = copy.deepcopy(self)
        next.final = final
        return next

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
            self.start[2].narrow(solver)

        for state in self.states:
            state.narrow(solver)

        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the transaction sequence."""
        for state in self.states:
            if isinstance(state.pc, int):  # SELFDESTRUCT balance transfer
                value = solver.evaluate(state.transaction.callvalue)
                yield f"SELFDESTRUCT\tvalue: {value}\n"
                continue

            yield from state.transaction.calldata.describe(solver)

            suffixes = list[str]()
            value = solver.evaluate(state.transaction.callvalue)
            if value > 0:
                yield f"\tvalue: {value}"
            caller = solver.evaluate(state.transaction.caller)
            player = solver.evaluate(self.player)
            if caller != player:
                yield "\tvia proxy"
                suffixes.append("via proxy")
            yield "\n"

            for call in state.calls:
                match call:
                    case GasHogCall():
                        yield "\tProxy CONSUME ALL GAS\n"
                    case DelegateCall():
                        ok = evaluate(solver, call.ok)
                        yield f"\tProxy {'RETURN' if ok else 'REVERT'} "
                        yield from call.returndata.describe(solver)
                        yield "\n"
                        if ok:
                            prev = evaluate(solver, call.previous_storage)
                            for k, v in evaluate(solver, call.next_storage).items():
                                if prev[k] != v:
                                    yield f"\tSet {hex(k)} to {hex(v)}\n"
                    case Call():
                        pass

        if self.final:
            for call in self.final.calls:
                match call:
                    case GasHogCall():
                        yield "Validate Proxy CONSUME ALL GAS\n"
                    case DelegateCall():
                        raise NotImplementedError
                    case Call():
                        pass


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
            elif name == "CODESIZE":
                continue
            elif name == "NUMBER":
                continue
            raise ValueError(f"validator depends on unsupported variable: {name}")

    def translate(self, history: History) -> Constraint:
        """Translate the validation constraint onto the given History."""
        if len(history.states) == 0:
            contracts, balances = history.start[0], history.start[1]
            number = Uint256(0)
        else:
            contracts = history.states[-1].contracts
            balances = history.states[-1].balances
            number = history.states[-1].block.number + Uint256(1)

        substitutions = dict[Any, Expression]()
        for name, term in self._constants.items():
            if name.startswith("STORAGE@"):
                addr = int(name[8:], 16)
                substitutions[term] = contracts[addr].storage
            elif name == "BALANCE":
                substitutions[term] = balances
            elif name == "CODESIZE":
                pass
            elif name == "NUMBER":
                substitutions[term] = number
            else:
                raise ValueError(f"unknown variable: {name}")

        return substitute(self.constraint, substitutions)
