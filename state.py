"""Classes for modeling contract execution."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional

import z3

from environment import Block, Contract, Universe
from sha3 import SHA3
from symbolic import Bytes, Constraint, check, uint8, uint160, uint256


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str

    block: Block
    contract: Contract
    universe: Universe
    sha3: SHA3

    pc: int
    stack: List[uint256]
    memory: Dict[int, uint8]  # concrete index -> 1-byte value

    address: uint160
    origin: uint160
    caller: uint160
    callvalue: uint256
    calldata: Bytes
    gasprice: uint256

    returndata: Bytes
    success: Optional[bool]

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    path_constraints: List[Constraint]

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int

    def copy(self) -> State:
        """Return a deep copy of this instance."""
        return State(
            suffix=self.suffix,
            block=self.block,
            contract=self.contract.copy(),
            universe=self.universe.copy(),
            sha3=self.sha3.copy(),
            pc=self.pc,
            stack=self.stack.copy(),
            memory=self.memory.copy(),
            address=self.address,
            origin=self.origin,
            caller=self.caller,
            callvalue=self.callvalue,
            calldata=self.calldata,
            gasprice=self.gasprice,
            returndata=self.returndata,
            success=self.success,
            path_constraints=self.path_constraints.copy(),
            path=self.path,
        )

    def constrain(self, solver: z3.Optimize, minimize: bool = False) -> None:
        """Apply accumulated constraints to the given solver instance."""
        if minimize:
            solver.minimize(self.callvalue)
            solver.minimize(self.calldata.length())

        # TODO: a contract could, in theory, call itself...
        solver.assert_and_track(self.address != self.origin, f"ADDROR{self.suffix}")
        solver.assert_and_track(self.address != self.caller, f"ADDRCL{self.suffix}")

        for i, constraint in enumerate(self.path_constraints):
            solver.assert_and_track(constraint, f"PC{i}{self.suffix}")

        self.sha3.constrain(solver)
        self.universe.constrain(solver)

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
                    addr != self.address,
                    self.universe.balances.peek(addr)
                    > since.universe.balances.peek(addr),
                ),
            ):
                return True

        return False
