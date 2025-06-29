"""Classes for modeling and checking solutions to the Ethernaut CTF."""

from __future__ import annotations

import copy
from functools import reduce
from typing import Iterable

from bytes import Bytes
from disassembler import abiencode
from environment import Contract, Transaction
from sequence import Sequence
from sha3 import SHA3
from smt import (
    Array,
    Constraint,
    Solver,
    Symbolic,
    Uint160,
    Uint256,
    get_symbols,
)
from snapshot import PLAYER, PROXY
from state import State, Termination
from universal import universal_transaction


class Validator:
    """For running validateInstance to check a proposed solution to a level."""

    transaction: Transaction
    constraint: Constraint | None
    constants: set[bytes] | None

    def __init__(self, sequence: Sequence, /, *, prints: bool = False) -> None:
        """
        Create a new Validator.

        For speed, we try to capture the logic of validateInstance in a succinct
        symbolic constraint. It's much faster to check a solution with `constraint`
        than it is to simulate a full call to validateInstance.
        """
        assert (arg0 := sequence.instance.reveal()) is not None
        assert (arg1 := PLAYER.reveal()) is not None
        calldata = (
            abiencode("validateInstance(address,address)")
            + arg0.to_bytes(32)
            + arg1.to_bytes(32)
        )
        self.transaction = Transaction(
            origin=PLAYER,
            caller=PLAYER,
            address=sequence.factory,
            calldata=Bytes(calldata),
        )
        self.constraint, self.carryover = None, None

        previous, block = sequence.states[-1], sequence.blocks[-1]
        start = State(
            suffix="-V",
            block=block,
            transaction=self.transaction,
            sha3=SHA3(),  # validator optimization requires this SHA3 go unused
            contracts={},
            balances=Array[Uint160, Uint256]("BALANCE"),
            solver=copy.deepcopy(previous.solver),
            mystery_proxy=PROXY,
            mystery_size=previous.mystery_size,
            gas_count=0,
            # ASSUMPTION: when executing validateInstance(...), we only call
            # into contracts defined at the outset, and no contract calls
            # itself.
            skip_self_calls=True,
        )

        for reference in previous.contracts.values():
            assert (a := reference.address.reveal()) is not None
            start = start.with_contract(
                Contract(
                    address=reference.address,
                    program=reference.program,
                    storage=Array[Uint256, Uint256](f"STORAGE@{a.to_bytes(20).hex()}"),
                    nonce=reference.nonce,
                ),
                True,
            )

        predicates = list[Constraint]()
        for end in universal_transaction(start, check=False, prints=prints):
            assert isinstance(end.pc, Termination)

            # This logic needs to match State.constrain(). We don't need to
            # worry about narrowing because SHA3 is not invoked (see check
            # below).
            b: Uint256 = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector()
            predicates.append(end.solver.constraint & (b != Uint256(0)))

            if len(end.contracts) > len(previous.contracts):
                # We can't handle validators that create contracts. That would
                # be pretty strange, though.
                raise NotImplementedError

            if end.sha3.free or end.sha3.symbolic:
                # We can't currently handle feeding the global SHA3 instance
                # into the validator. Fall back to running validateInstance with
                # concrete inputs at every step.
                return

        assert predicates
        constraint = reduce(lambda p, q: p | q, predicates, Constraint(False))
        constants = set(get_symbols(constraint).keys())
        for name in constants:
            if name.startswith(b"STORAGE@"):
                continue
            elif name == b"BALANCE":
                continue
            elif name == b"CODESIZE":
                continue
            elif name == b"NUMBER":
                continue
            else:
                # Validator expression uses an unsupported variable; fall back.
                return
        self.constraint, self.constants = constraint, constants

    def _translate(self, sequence: Sequence) -> Constraint | None:
        """Translate the validation constraint onto the given Sequence."""
        if self.constraint is None:
            return None
        assert self.constants is not None

        substitutions = dict[bytes, Symbolic]()
        for name in self.constants:
            if name.startswith(b"STORAGE@"):
                addr = int(name[8:], 16)
                if addr in sequence.states[-1].contracts:
                    substitutions[name] = sequence.states[-1].contracts[addr].storage
                else:
                    substitutions[name] = Array[Uint256, Uint256](Uint256(0))
            elif name == b"BALANCE":
                substitutions[name] = sequence.states[-1].balances
            elif name == b"CODESIZE":
                pass
            elif name == b"NUMBER":
                substitutions[name] = sequence.blocks[len(sequence.states) - 1].number
            else:
                raise ValueError(f"unknown variable: {name}")

        return self.constraint.substitute(substitutions)

    def check(self, sequence: Sequence, /, *, prints: bool = False) -> Solution | None:
        """Simulate the execution of validateInstance on the given sequence."""
        translated = self._translate(sequence)
        if translated is not None:
            solver = copy.deepcopy(sequence.solver)
            solver.add(translated)
            if solver.check():
                sequence.narrow(solver)
                return Solution(sequence, solver, None)
            return None

        previous, block = sequence.states[-1], sequence.blocks[-1]
        start = State(
            suffix="-V",
            block=block,
            transaction=self.transaction,
            sha3=copy.deepcopy(previous.sha3),
            contracts=copy.deepcopy(previous.contracts),
            balances=copy.deepcopy(previous.balances),
            solver=copy.deepcopy(previous.solver),
            mystery_proxy=PROXY,
            mystery_size=previous.mystery_size,
            gas_count=0,
        )

        # Allow validateInstance(...) to call back into the factory contract.
        # This is done in Double Entry Point in order to invoke a helper
        # function, for example.
        assert (address := self.transaction.address.reveal()) is not None
        start.contracts[address].invisible = False

        for end in universal_transaction(start, check=False, prints=prints):
            assert isinstance(end.pc, Termination)
            solver = end.solver
            candidate = sequence.extend(end)
            ok = end.pc.returndata.slice(
                Uint256(0), Uint256(32)
            ).bigvector() != Uint256(0)
            solver.add(ok)
            if solver.check():
                candidate.narrow(solver)
                return Solution(sequence, solver, end)
        return None


class Solution:
    """Represents a full solution to an Ethernaut level."""

    sequence: Sequence
    solver: Solver
    validate: State | None

    def __init__(
        self, sequence: Sequence, solver: Solver, validate: State | None
    ) -> None:
        """Create a new Solution."""
        self.sequence = sequence
        self.solver = solver
        self.validate = validate

    def describe(self) -> Iterable[str]:
        """Yield a human-readable description of the Solution."""
        yield from self.sequence.describe(self.solver)

        if self.validate is None:
            return
        assert self.validate.mystery_proxy is not None

        post = False
        for call in self.validate.calls:
            for line in call.describe(self.solver, self.validate.mystery_proxy):
                if not post:
                    yield "validateInstance(...)\n"
                    post = True
                yield line
