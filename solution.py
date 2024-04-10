"""Classes for modeling and checking solutions to the Ethernaut CTF."""

from __future__ import annotations

from functools import reduce
from typing import Any, Iterable

from bytes import Bytes
from disassembler import abiencode
from environment import ConcreteContract, Transaction
from sequence import Sequence
from sha3 import SHA3
from smt import (
    Array,
    BitwuzlaTerm,
    ConstrainingError,
    Constraint,
    Expression,
    Solver,
    Uint160,
    Uint256,
    get_constants,
    substitute,
)
from snapshot import PLAYER, PROXY
from state import State, Termination
from universal import universal_transaction


class Validator:
    """For running validateInstance to check a proposed solution to a level."""

    transaction: Transaction
    constraint: Constraint | None
    constants: dict[str, BitwuzlaTerm] | None

    def __init__(self, sequence: Sequence, prints: bool = False) -> None:
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

        carryover, block = sequence.subsequent(validation=True)
        start = State(
            suffix="-V",
            block=block,
            transaction=self.transaction,
            sha3=SHA3(),  # validator optimization requires this SHA3 go unused
            contracts={},
            balances=Array[Uint160, Uint256]("BALANCE"),
            constraint=carryover.constraint,
            mystery_proxy=PROXY,
            mystery_size=carryover.mystery_size,
            gas_count=0,
            # ASSUMPTION: when executing validateInstance(...), we only call
            # into contracts defined at the outset, and no contract calls
            # itself.
            skip_self_calls=True,
        )

        for reference in carryover.contracts.values():
            assert (a := reference.address.reveal()) is not None
            assert isinstance(reference, ConcreteContract)
            start = start.with_contract(
                ConcreteContract(
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
            predicates.append(end.constraint & (b != Uint256(0)))

            if len(end.contracts) > len(carryover.contracts):
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
        constants = get_constants(constraint)
        for name in constants.keys():
            if name.startswith("STORAGE@"):
                continue
            elif name == "BALANCE":
                continue
            elif name == "CODESIZE":
                continue
            elif name == "NUMBER":
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

        substitutions = dict[Any, Expression]()
        for name, term in self.constants.items():
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

    def check(self, sequence: Sequence) -> Solution:
        """Simulate the execution of validateInstance on the given sequence."""
        translated = self._translate(sequence)
        if translated is not None:
            return Solution(sequence, translated)

        carryover, block = sequence.subsequent(validation=True)
        start = State(
            suffix="-V",
            block=block,
            transaction=self.transaction,
            sha3=carryover.sha3,
            contracts=carryover.contracts,
            balances=carryover.balances,
            constraint=carryover.constraint,
            mystery_proxy=PROXY,
            mystery_size=carryover.mystery_size,
            gas_count=0,
        )

        for end in universal_transaction(start):
            assert isinstance(end.pc, Termination)
            solver = Solver()
            candidate = sequence.extend(end)
            candidate.constrain(solver, check=False)
            ok = end.pc.returndata.slice(
                Uint256(0), Uint256(32)
            ).bigvector() != Uint256(0)
            solver.add(ok)
            if solver.check():
                end.sha3.narrow(solver)
                return Solution(sequence, end)
        return Solution(sequence, None)


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
        if isinstance(self.validate, State):
            self.validate.narrow(solver)
        self.sha3.narrow(solver)
        assert solver.check()

    def describe(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable description of the Solution."""
        yield from self.sequence.describe(solver)

        if isinstance(self.validate, State):
            assert self.validate.mystery_proxy is not None
            post = False
            for call in self.validate.calls:
                for line in call.describe(solver, self.validate.mystery_proxy):
                    if not post:
                        yield "validateInstance(...)\n"
                        post = True
                    yield line
