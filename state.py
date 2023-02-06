"""Classes for modeling contract execution."""

from __future__ import annotations

from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass
from itertools import count
from typing import Iterator, List, Optional, Tuple

from arrays import FrozenBytes, MutableBytes
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from smt import Constraint, Uint160, Uint256
from solver import Solver


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str

    block: Block
    contract: Contract
    transaction: Transaction
    universe: Universe
    sha3: SHA3

    pc: int
    stack: List[Uint256]
    memory: MutableBytes

    returndata: FrozenBytes
    success: Optional[bool]

    subcontexts: List[State]

    # Every time the GAS instruction is invoked we return a symbolic result,
    # tracked here. These should be monotonically decreasing.
    gas_variables: List[Uint256]

    # Every time the CALL instruction is invoked we return a symbolic result,
    # tracked here.
    call_variables: List[Tuple[FrozenBytes, Constraint]]

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    path_constraints: List[Constraint]

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

        for i in range(1, len(self.gas_variables)):
            solver.assert_and_track(self.gas_variables[i - 1] >= self.gas_variables[i])

        self.sha3.constrain(solver)
        self.universe.constrain(solver)

    def narrow(self, solver: Solver) -> None:
        """Apply concrete constraints to a given model instance."""
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
        for i in count():
            constraint = self.transaction.calldata.length == Uint256(i)
            if solver.check(constraint):
                solver.assert_and_track(constraint)
                break

        # Minimize callvalue
        for i in count():
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

    def evaluate(self, solver: Solver) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        r: OrderedDict[str, str] = OrderedDict()
        a = solver.evaluate(self.contract.address)
        if a is not None and a.unwrap() > 0:
            r["Address"] = "0x" + a.unwrap(bytes).hex()
        returndata = self.returndata.evaluate(solver, True)
        if returndata:
            r["Return"] = "0x" + returndata
        return r

    @contextmanager
    def descend(self, contract: Contract, transaction: Transaction) -> Iterator[State]:
        """Descend into a subcontext."""
        substate = State(
            suffix=f"{len(self.subcontexts)}.{self.suffix}",
            block=self.block,
            contract=contract,
            transaction=transaction,
            universe=self.universe,
            sha3=self.sha3,
            pc=0,
            stack=[],
            memory=MutableBytes.concrete(b""),
            success=None,
            returndata=FrozenBytes.concrete(b""),
            subcontexts=[],
            gas_variables=self.gas_variables,
            call_variables=self.call_variables,
            path_constraints=self.path_constraints,
            path=self.path,
        )
        substate.universe.transfer(
            transaction.caller, contract.address, transaction.callvalue
        )
        self.subcontexts.append(substate)

        yield substate

        # TODO: support reentrancy (apply storage changes to contract)

        self.returndata = substate.returndata
        self.gas_variables = substate.gas_variables
        self.call_variables = substate.call_variables
        self.path_constraints = substate.path_constraints
        self.path = substate.path
