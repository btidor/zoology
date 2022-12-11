"""Classes for modeling contract execution."""

from __future__ import annotations

from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator, List, Optional

import z3

from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from symbolic import (
    BA,
    Bytes,
    Constraint,
    check,
    is_concrete,
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
    memory: Bytes

    returndata: Bytes
    success: Optional[bool]

    subcontexts: List[State]

    # Every time the GAS instruction is invoked we return a symbolic result,
    # tracked here. These should be monotonically decreasing.
    gas_variables: List[z3.BitVecRef]

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
            solver.minimize(self.transaction.calldata.length)

        for i, constraint in enumerate(self.path_constraints):
            solver.assert_and_track(constraint, f"PC{i}{self.suffix}")

        # ASSUMPTION: the current block number is at least 256. This prevents
        # the BLOCKHASH instruction from overflowing.
        solver.assert_and_track(z3.UGE(self.block.number, 256), f"NUMLIM{self.suffix}")

        for i in range(1, len(self.gas_variables)):
            solver.assert_and_track(
                z3.UGE(self.gas_variables[i - 1], self.gas_variables[i]),
                f"MONOGAS{i}{self.suffix}",
            )

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
                    z3.UGT(
                        self.universe.balances.peek(addr),
                        since.universe.balances.peek(addr),
                    ),
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

    @contextmanager
    def descend(self, contract: Contract, transaction: Transaction) -> Iterator[State]:
        """Descend into a subcontext."""
        context = State(
            suffix=f"{len(self.subcontexts)}.{self.suffix}",
            block=self.block,
            contract=contract,
            transaction=transaction,
            universe=self.universe,
            sha3=self.sha3,
            pc=0,
            stack=[],
            memory=Bytes.concrete(b""),
            success=None,
            returndata=Bytes.concrete(b""),
            subcontexts=[],
            gas_variables=self.gas_variables,
            path_constraints=self.path_constraints,
            path=self.path,
        )
        context.universe.transfer(
            transaction.caller, contract.address, transaction.callvalue
        )
        self.subcontexts.append(context)

        yield context

        self.gas_variables = context.gas_variables
        self.path_constraints = context.path_constraints
        self.path = context.path
