from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, cast

import z3

from _hash import SHA3
from _symbolic import ByteArray, Constraint, do_check, uint8, uint160, uint256
from _universe import Block, Contract, Universe


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
    calldata: ByteArray
    gasprice: uint256

    returndata: List[z3.BitVecRef]
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
            contract=self.contract,
            universe=self.universe,
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

    # def is_changed(self, solver: z3.Optimize, since: State) -> bool:
    #     assert self.success is True

    #     # TODO: constrain further to eliminate no-op writes?
    #     if len(self.storage.written) > 0:
    #         return True

    #     # Check if any address other than the contract itself has increased
    #     for addr in self.balances.written:
    #         if do_check(
    #             solver,
    #             z3.And(
    #                 addr != self.address,
    #                 cast(z3.BitVecRef, self.balances.array[addr])
    #                 > cast(z3.BitVecRef, since.balances.array[addr]),
    #             ),
    #         ):
    #             return True

    #     return False
