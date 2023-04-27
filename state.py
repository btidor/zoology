"""Classes for modeling contract execution."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from typing import Callable

from environment import Block, Contract, Transaction, Universe
from smt.arrays import FrozenBytes, MutableBytes
from smt.sha3 import SHA3
from smt.smt import Constraint, Uint160, Uint256
from smt.solver import Solver


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str

    block: Block
    contract: Contract
    transaction: Transaction
    universe: Universe
    sha3: SHA3

    pc: int | Termination
    stack: list[Uint256]
    memory: MutableBytes

    # Tracks the number of times we've spawned a subcontext, so that symbolic
    # variables can be given a unique name.
    children: int

    # The return data of the most recent subcontext, for the RETURNDATASIZE and
    # RETURNDATACOPY instructions.
    latest_return: FrozenBytes

    logs: list[Log]

    # Every time the GAS instruction is invoked we return a symbolic result,
    # tracked here. These should be monotonically decreasing. In the case of a
    # concrete execution, this value is set to None.
    gas_variables: list[Uint256] | None

    # Every time the CALL instruction is invoked we return a symbolic result,
    # tracked here.
    call_variables: list[tuple[FrozenBytes, Constraint]]

    # List of constraints that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    path_constraints: list[Constraint]

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int

    def px(self) -> str:
        """Return a human-readable version of the path."""
        return "Px" + hex(self.path)[2:].upper()

    def constrain(self, solver: Solver) -> None:
        """Apply accumulated constraints to the given solver instance."""
        for i, constraint in enumerate(self.path_constraints):
            solver.assert_and_track(constraint)

        # ASSUMPTION: the current block number is at least 256. This prevents
        # the BLOCKHASH instruction from overflowing.
        solver.assert_and_track(self.block.number >= Uint256(256))

        if self.gas_variables is not None:
            for i in range(1, len(self.gas_variables)):
                solver.assert_and_track(
                    self.gas_variables[i - 1] >= self.gas_variables[i]
                )

        self.sha3.constrain(solver)
        self.universe.constrain(solver)

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given model instance."""
        constraint = self.contract.address == Uint160(
            0xADADADADADADADADADADADADADADADADADADADAD
        )
        if solver.check(constraint):
            solver.assert_and_track(constraint)

        constraint = self.transaction.caller == Uint160(
            0xCACACACACACACACACACACACACACACACACACACACA
        )

        if solver.check(constraint):
            solver.assert_and_track(constraint)

        # Minimize calldata length
        for i in range(257):
            constraint = self.transaction.calldata.length == Uint256(i)
            if solver.check(constraint):
                solver.assert_and_track(constraint)
                break

        # Minimize callvalue
        for i in range(1025):
            constraint = self.transaction.callvalue == Uint256(i)
            if solver.check(constraint):
                solver.assert_and_track(constraint)
                break

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
        if a is not None and a.unwrap() > 0:
            r["Address"] = "0x" + a.unwrap(bytes).hex()
        returndata = self.pc.returndata.describe(solver, True)
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
    topics: list[Uint256]


class ControlFlow:
    """A superclass for control-flow actions."""

    pass


@dataclass(frozen=True)
class Jump(ControlFlow):
    """A JUMP or JUMPI instruction."""

    targets: list[tuple[Constraint, State]]


@dataclass(frozen=True)
class Descend(ControlFlow):
    """A CALL, DELEGATECALL, etc. instruction."""

    state: State
    callback: Callable[[State, State], State]

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
            suffix=f"{state.children}.{state.suffix}",
            block=state.block,
            contract=contract,
            transaction=transaction,
            universe=state.universe,
            sha3=state.sha3,
            pc=0,
            stack=[],
            memory=MutableBytes.concrete(b""),
            children=0,
            latest_return=FrozenBytes.concrete(b""),
            logs=state.logs,
            gas_variables=state.gas_variables,
            call_variables=state.call_variables,
            path_constraints=state.path_constraints,
            path=state.path,
        )
        substate.universe.transfer(
            transaction.caller, contract.address, transaction.callvalue
        )
        state.children += 1

        def metacallback(state: State, substate: State) -> State:
            # TODO: support reentrancy (apply storage changes to contract,
            # including on self-calls)
            assert isinstance(substate.pc, Termination)
            state.logs = substate.logs
            state.latest_return = substate.pc.returndata
            state.gas_variables = substate.gas_variables
            state.call_variables = substate.call_variables
            state.path_constraints = substate.path_constraints
            state.path = substate.path
            return callback(state, substate)

        return Descend(substate, metacallback)
