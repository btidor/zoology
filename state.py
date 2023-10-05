"""Classes for modeling contract execution."""

from __future__ import annotations

import copy
from collections import OrderedDict, defaultdict
from dataclasses import dataclass, field
from typing import Any, Callable

from bytes import FrozenBytes, MutableBytes
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from smt import (
    Array,
    Constraint,
    Solver,
    Uint160,
    Uint256,
    overflow_safe,
    underflow_safe,
)


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str = ""

    block: Block = field(default_factory=Block)
    contract: Contract = field(default_factory=Contract)
    transaction: Transaction = field(default_factory=Transaction)
    universe: Universe = field(default_factory=Universe)
    sha3: SHA3 = field(default_factory=SHA3)

    pc: int | Termination = 0
    stack: list[Uint256] = field(default_factory=list)
    memory: MutableBytes = field(default_factory=MutableBytes.concrete)

    # Tracks the number of times we've spawned a subcontext, so that symbolic
    # variables can be given a unique name.
    children: int = 0

    # The return data of the most recent subcontext, for the RETURNDATASIZE and
    # RETURNDATACOPY instructions.
    latest_return: FrozenBytes = FrozenBytes.concrete()

    logs: list[Log] = field(default_factory=list)

    # Every time the GAS instruction is invoked we return a symbolic result,
    # suffixed with this counter to make it unique. In the case of a concrete
    # execution, this value is set to None.
    #
    # ASSUMPTION: because we do not track gas consumption, we place no
    # constraints whatsoever on the gas variables.
    #
    gas_count: int | None = None

    # Every time the CALL instruction is invoked with a symbolic address we
    # return a symbolic result, suffixed with this counter to make it unique.
    call_count: int = 0

    # Every time the DELEGATECALL instruction is invoked with a symbolic address
    # we return a symbolic result, suffixed with this counter to make it unique
    delegates: tuple[DelegateCall, ...] = ()

    # Symbolic constraint that must be satisfied in order for the program to
    # reach this state. Largely based on the JUMPI instructions (if statements)
    # encountered in the execution.
    constraint: Constraint = field(default=Constraint(True))

    # Symbolic constraint that must be satisfied in order for narrowing to
    # succeed. Currently used to check that DELEGATECALL to a symbolic address
    # can be fully controlled.
    narrower: Constraint = field(default=Constraint(True))

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    # Tracks the number of times each JUMPI instruction has been reached. States
    # are prioritized by their cost, which is computed as the sum of the branch
    # counts, exponentially weighted to penalize long or infinite loops.
    branching: dict[int, int] = field(default_factory=lambda: defaultdict(lambda: 0))
    cost: int = 0

    # If this State represents a subcontext, this callback should be called upon
    # termination. It takes a copy of this State as an argument and returns the
    # parent context as it should be resumed.
    recursion: Callable[[State], State] | None = None

    def px(self) -> str:
        """Return a human-readable version of the path."""
        return "Px" + hex(self.path)[2:].upper()

    def __post__init__(self) -> None:
        """Initialize starting constraints."""
        # ASSUMPTION: the current block number is at least 256. This prevents
        # the BLOCKHASH instruction from overflowing.
        self.constraint &= self.block.number >= Uint256(256)

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, State):
            return NotImplemented
        return self.cost < other.cost

    def transfer(self, src: Uint160, dst: Uint160, val: Uint256) -> None:
        """Transfer value from one account to another."""
        if val.reveal() == 0:
            return

        # ASSUMPTION: If `balances[src]` drops below zero, execution will
        # revert. Therefore, `balances[src] >= val`.
        self.constraint &= underflow_safe(self.universe.balances[src], val)
        # ASSUMPTION: There isn't enough ETH in existence to overflow an
        # account's balance; all balances are less than 2^255 wei.
        self.constraint &= overflow_safe(self.universe.balances[dst], val)

        self.universe.balances[src] -= val
        self.universe.balances[dst] += val

    def constrain(self, solver: Solver) -> None:
        """Apply accumulated constraints to the given solver instance."""
        solver.add(self.constraint)
        self.sha3.constrain(solver)

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given model instance."""
        constraint = self.contract.address == Uint160(
            0xADADADADADADADADADADADADADADADADADADADAD
        )
        if solver.check(constraint):
            solver.add(constraint)

        constraint = self.transaction.caller == Uint160(
            0xCACACACACACACACACACACACACACACACACACACACA
        )

        if solver.check(constraint):
            solver.add(constraint)

        # Minimize calldata length
        for i in range(257):
            constraint = self.transaction.calldata.length == Uint256(i)
            if solver.check(constraint):
                solver.add(constraint)
                break

        # Minimize callvalue
        for i in range(257):
            constraint = self.transaction.callvalue == Uint256(2**i - 1)
            if solver.check(constraint):
                solver.add(constraint)
                break

        solver.add(self.narrower)
        assert solver.check()

    def is_changed(self, since: State) -> bool:
        """Check if any permanent state changes have been made."""
        # TODO: constrain further to eliminate no-op writes?
        if len(self.contract.storage.written) > 0:
            return True

        # Check if any address other than the contract itself has increased
        solver = Solver()
        self.constrain(solver)
        for addr in self.universe.balances.written:
            if solver.check(
                addr != self.contract.address,
                self.universe.balances.peek(addr) > since.universe.balances.peek(addr),
            ):
                return True

        return False

    def describe(self, solver: Solver) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        assert isinstance(self.pc, Termination)
        r: OrderedDict[str, str] = OrderedDict()
        a = solver.evaluate(self.contract.address)
        if a > 0:
            r["Address"] = "0x" + a.to_bytes(20).hex()
        returndata = self.pc.returndata.describe(solver)
        if returndata:
            r["Return"] = "0x" + returndata
        return r


@dataclass(frozen=True)
class Termination:
    """The result of running a contract to completion."""

    success: bool
    returndata: FrozenBytes


@dataclass(frozen=True)
class Log:
    """A log entry emitted by the LOG* instruction."""

    data: FrozenBytes
    topics: tuple[Uint256, ...]


@dataclass(frozen=True)
class DelegateCall:
    """Information about a symbolic DELEGATECALL instruction."""

    ok: Constraint
    returndata: FrozenBytes
    previous_storage: Array[Uint256, Uint256]
    next_storage: Array[Uint256, Uint256]


class ControlFlow:
    """A superclass for control-flow actions."""

    pass


@dataclass(frozen=True)
class Jump(ControlFlow):
    """A JUMPI instruction that branches the control flow."""

    targets: tuple[State, ...]


@dataclass(frozen=True)
class Descend(ControlFlow):
    """A CALL, DELEGATECALL, etc. instruction."""

    state: State

    @classmethod
    def new(
        cls,
        state: State,
        contract: Contract,
        transaction: Transaction,
        callback: Callable[[State, State], State],
    ) -> Descend:
        """Descend into a subcontext."""
        substate = State(
            suffix=f"{state.suffix}-{state.children}",
            block=state.block,
            contract=contract,
            transaction=transaction,
            universe=state.universe,
            sha3=state.sha3,
            logs=state.logs,
            gas_count=state.gas_count,
            call_count=state.call_count,
            delegates=state.delegates,
            constraint=state.constraint,
            narrower=state.narrower,
            path=state.path,
            cost=state.cost,
        )
        substate.transfer(transaction.caller, contract.address, transaction.callvalue)
        state.children += 1

        def metacallback(substate: State) -> State:
            # TODO: support reentrancy (apply storage changes to contract,
            # including on self-calls)
            assert isinstance(substate.pc, Termination)
            next = copy.deepcopy(state)
            next.logs = substate.logs
            next.latest_return = substate.pc.returndata
            next.gas_count = substate.gas_count
            next.call_count = substate.call_count
            next.delegates = substate.delegates
            next.constraint = substate.constraint
            next.narrower = substate.narrower
            next.path = substate.path
            next.cost = substate.cost
            return callback(next, substate)

        substate.recursion = metacallback
        return Descend(substate)
