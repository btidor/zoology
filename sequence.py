"""Classes for modeling a sequence of multiple transactions."""

from __future__ import annotations

import copy
from dataclasses import dataclass
from typing import Any, Iterable

from environment import Block, Contract, Transaction
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


@dataclass
class Next:
    """Represents the information carried from one transaction to the next."""

    constraint: Constraint
    contracts: dict[int, Contract]
    balances: Array[Uint160, Uint256]
    sha3: SHA3

    @classmethod
    def from_state(cls, state: State) -> Next:
        """Extract carryover information from a State."""
        return Next(state.constraint, state.contracts, state.balances, state.sha3)

    def clone_and_reset(self) -> Next:
        """Clone this Next and reset array access tracking."""
        return Next(
            self.constraint,
            {k: v.clone_and_reset() for (k, v) in self.contracts.items()},
            self.balances.clone_and_reset(),
            copy.deepcopy(self.sha3),
        )


class Sequence:
    """Represents a linear sequence of synthetic transactions."""

    factory: Uint160
    instance: Uint160
    player: Uint160
    proxy: Uint160
    blocks: list[Block]

    create: State | None  # the concrete createInstance call
    states: list[State]  # synthetic transactions

    next: Next
    validate_transaction: Transaction

    def __init__(
        self,
        factory: Uint160,
        instance: Uint160,
        player: Uint160,
        proxy: Uint160,
        start: State,
        validate_transaction: Transaction,
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

        self.create = start
        self.states = list[State]()

        self.next = Next.from_state(start)
        self.validate_transaction = validate_transaction

    def __deepcopy__(self, memo: Any) -> Sequence:
        result = copy.copy(self)
        result.states = copy.copy(result.states)
        return result

    def pz(self) -> str:
        """Return a human-readable version of the sequence of paths."""
        return "Pz" + ":".join(map(lambda s: s.px()[2:], self.states))

    def subsequent(self, validation: bool = False) -> tuple[Next, Block]:
        """Set up the execution of a new transaction."""
        return self.next.clone_and_reset(), self.peek_next_block(validation)

    def peek_next_block(self, validation: bool = False) -> Block:
        """Return the next block."""
        return self.blocks[-1 if validation else len(self.states)]

    def extend(self, state: State) -> Sequence:
        """Add a new transaction to the Sequence."""
        result = copy.deepcopy(self)
        result.states.append(state)
        result.next = Next.from_state(state)
        if len(result.states) > 15:
            raise OverflowError("sequence is limited to 15 states")
        return result

    def constrain(self, solver: Solver, check: bool = True) -> None:
        """Apply hard constraints to the given solver instance."""
        solver.add(self.next.constraint)
        if check and not solver.check():
            raise ConstrainingError

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        for state in self.states:
            state.narrow(solver)
        self.next.sha3.narrow(solver)
        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the Sequence."""
        for state in self.states:
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


class Solution:
    """Represents a full solution to an Ethernaut level."""

    sequence: Sequence
    validate: State | Constraint | None
    sha3: SHA3

    def __init__(self, sequence: Sequence, validate: State | Constraint | None) -> None:
        """Create a new Solution."""
        self.sequence = sequence
        self.validate = validate
        match validate:
            case State():
                self.sha3 = validate.sha3
            case Constraint() | None:
                self.sha3 = sequence.next.sha3

    def constrain(self, solver: Solver, check: bool = True) -> None:
        """Apply hard constraints to the given solver instance."""
        match self.validate:
            case State():
                solver.add(self.validate.constraint)
            case Constraint():
                self.sequence.constrain(solver, check=False)
                solver.add(self.validate)
            case None:
                solver.add(Constraint(False))

        if check and not solver.check():
            raise ConstrainingError

    def narrow(self, solver: Solver) -> None:
        """Apply soft and deferred constraints to a given solver instance."""
        for state in self.sequence.states:
            state.narrow(solver)
        self.sha3.narrow(solver)
        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the Solution."""
        yield from self.sequence.describe(solver)

        if isinstance(self.validate, State):
            for call in self.validate.calls:
                match call:
                    case GasHogCall():
                        yield "Validate Proxy CONSUME ALL GAS\n"
                    case DelegateCall():
                        raise NotImplementedError
                    case Call():
                        pass


class Validator:
    """
    Represents the result of running validateInstance.

    A Validator captures the logic of validateInstance in a succinct symbolic
    constraint. It's much faster to check a solution with a Validator than it is
    to simulate a full call to validateInstance.
    """

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

    def translate(self, sequence: Sequence) -> Constraint:
        """Translate the validation constraint onto the given Sequence."""
        substitutions = dict[Any, Expression]()
        for name, term in self._constants.items():
            if name.startswith("STORAGE@"):
                addr = int(name[8:], 16)
                substitutions[term] = sequence.next.contracts[addr].storage
            elif name == "BALANCE":
                substitutions[term] = sequence.next.balances
            elif name == "CODESIZE":
                pass
            elif name == "NUMBER":
                substitutions[term] = sequence.peek_next_block().number
            else:
                raise ValueError(f"unknown variable: {name}")

        return substitute(self.constraint, substitutions)
