"""Classes for modeling contract execution."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
from typing import Dict, List, Optional

import z3

from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from symbolic import (
    BA,
    Bytes,
    Constraint,
    check,
    is_concrete,
    uint8,
    uint256,
    unwrap,
    unwrap_bytes,
    zeval,
)


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
    stack: List[uint256]
    memory: Dict[int, uint8]  # concrete index -> 1-byte value

    returndata: Bytes
    success: Optional[bool]

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    path_constraints: List[Constraint]

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int

    def constrain(self, solver: z3.Optimize, minimize: bool = False) -> None:
        """Apply accumulated constraints to the given solver instance."""
        if minimize:
            solver.minimize(self.transaction.callvalue)
            solver.minimize(self.transaction.calldata.length())

        # TODO: a contract could, in theory, call itself...
        solver.assert_and_track(
            self.contract.address != self.transaction.origin, f"ADDROR{self.suffix}"
        )
        solver.assert_and_track(
            self.contract.address != self.transaction.caller, f"ADDRCL{self.suffix}"
        )

        for i, constraint in enumerate(self.path_constraints):
            solver.assert_and_track(constraint, f"PC{i}{self.suffix}")

        self.sha3.constrain(solver)
        self.universe.constrain(solver)

    def narrow(self, solver: z3.Optimize, model: z3.ModelRef) -> z3.ModelRef:
        """Apply concrete constraints to a given model instance."""
        constraint = self.contract.address == BA(
            0xADADADADADADADADADADADADADADADADADADADAD
        )
        if check(solver, constraint):
            solver.assert_and_track(constraint, "DEFAULT.ADDRESS")
            assert check(solver)
            model = solver.model()

        constraint = self.transaction.caller == BA(
            0xCACACACACACACACACACACACACACACACACACACACA
        )
        if check(solver, constraint):
            solver.assert_and_track(constraint, "DEFAULT.CALLER")
            assert check(solver)
            model = solver.model()

        check(solver)
        return self.sha3.narrow(solver, model)

    def is_changed(self, solver: z3.Optimize, since: State) -> bool:
        """Check if any permanent state changes have been made."""
        # TODO: constrain further to eliminate no-op writes?
        if len(self.contract.storage.written) > 0:
            return True

        # Check if any address other than the contract itself has increased
        for addr in self.universe.balances.written:
            if check(
                solver,
                z3.And(
                    addr != self.contract.address,
                    self.universe.balances.peek(addr)
                    > since.universe.balances.peek(addr),
                ),
            ):
                return True

        return False

    def evaluate(self, model: z3.ModelRef) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        r: OrderedDict[str, str] = OrderedDict()
        a = zeval(model, self.contract.address)
        if is_concrete(a) and unwrap(a) > 0:
            r["Address"] = "0x" + unwrap_bytes(a).hex()
        returndata = self.returndata.evaluate(model, True)
        if returndata:
            r["Return"] = "0x" + returndata
        return r
