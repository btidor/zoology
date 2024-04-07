"""Classes for modeling contract execution."""

from __future__ import annotations

from collections import OrderedDict, defaultdict
from dataclasses import dataclass, field
from typing import Any, Callable

from bytes import BYTES, Bytes, Memory
from disassembler import Program
from environment import Block, ConcreteContract, Contract, Transaction
from sha3 import SHA3
from smt import (
    Array,
    Constraint,
    Solver,
    Uint8,
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
    transaction: Transaction = field(default_factory=Transaction)
    sha3: SHA3 = field(default_factory=SHA3)

    # ASSUMPTION: all contract accounts are listed here. All other addresses are
    # either EOAs or are uncreated.
    contracts: dict[int, Contract] = field(default_factory=dict)  # address -> Contract
    balances: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256](Uint256(0))
    )

    pc: int | Termination = 0
    stack: list[Uint256] = field(default_factory=list)
    memory: Memory = field(default_factory=Memory)
    logs: list[Log] = field(default_factory=list)

    # The return data of the most recent subcontext, for the RETURNDATASIZE and
    # RETURNDATACOPY instructions.
    latest_return: Bytes = Bytes()

    # Every(-ish) time a CALL, DELEGATECALL, etc. instruction is invoked we
    # return a symbolic result, tracked here.
    calls: tuple[Call, ...] = ()

    # During instructions like CREATE and DELEGATECALL, the contract runs with
    # code not associated with its address (e.g. initcode).
    program_override: Program | None = None

    # In addition to CALLing to a concrete, registered contract, we can
    # optionally model a CALL to a symbolic "proxy" contract that returns a
    # fully-symbolic response.
    mystery_proxy: Uint160 | None = None
    mystery_size: Uint256 | None = None

    # Every time the GAS instruction is invoked we return a symbolic result,
    # suffixed with this counter to make it unique. In the case of a concrete
    # execution, this value is set to None.
    #
    # ASSUMPTION: because we do not track gas consumption, we place no
    # constraints whatsoever on the gas variables.
    #
    gas_count: int | None = None
    gas_hogged: Uint256 = Uint256(0)

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

    # Whether the contract has mutated the state of the blockchain so far.
    # During a STATICCALL, this variable is set to None so that stores and
    # transfers raise an exception.
    changed: bool | None = False

    # We want to raise an exception if a contract tries to call itself during
    # the validate function (i.e. with fully symbolic state), since this usually
    # indicates that the solver is entering an infinite loop.
    skip_self_calls: bool = False

    def px(self) -> str:
        """Return a human-readable version of the path."""
        return "Px" + hex(self.path)[2:].upper()

    def __post_init__(self) -> None:
        # ASSUMPTION: the current block number is at least 256. This prevents
        # the BLOCKHASH instruction from overflowing.
        self.constraint &= self.block.number >= Uint256(256)
        if self.mystery_proxy is not None:
            assert (
                self.mystery_proxy.reveal() is not None
            ), "State requires concrete mystery proxy address, if present"

    @property
    def program(self) -> Program:
        """Return the currently-executing program."""
        if self.program_override is not None:
            return self.program_override
        assert (address := self.transaction.address.reveal()) is not None
        assert isinstance((contract := self.contracts[address]), ConcreteContract)
        return contract.program

    @property
    def storage(self) -> Array[Uint256, Uint256]:
        """Return the current contract's storage."""
        assert (address := self.transaction.address.reveal()) is not None
        return self.contracts[address].storage

    def with_contract(
        self, contract: Contract | Program, overwrite: bool = False
    ) -> State:
        """Add a contract to the state."""
        if isinstance(contract, Program):
            contract = ConcreteContract(program=contract)
        assert (address := contract.address.reveal()) is not None
        if self.mystery_proxy is not None and address == self.mystery_proxy.reveal():
            raise KeyError(
                f"Contract 0x{address.to_bytes(20).hex()} shadows mystery proxy"
            )
        if address in self.contracts and not overwrite:
            raise KeyError(f"Contract 0x{address.to_bytes(20).hex()} already exists")
        self.contracts[address] = contract
        return self

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, State):
            return NotImplemented
        return self.cost < other.cost

    def transfer(
        self, src: Uint160, dst: Uint160, val: Uint256, initial: bool = False
    ) -> None:
        """Transfer value from one account to another."""
        if val.reveal() == 0:
            return
        elif self.changed is None:
            raise ValueError("Nonzero transfer is forbidden during a STATICCALL")

        # ASSUMPTION: if `balances[src]` drops below zero, execution will
        # revert. Therefore, `balances[src] >= val`.
        self.constraint &= underflow_safe(self.balances[src], val)
        # ASSUMPTION: there isn't enough ETH in existence to overflow an
        # account's balance; all balances are less than 2^255 wei.
        self.constraint &= overflow_safe(self.balances[dst], val)

        self.balances[src] -= val
        self.balances[dst] += val
        if not initial:
            self.changed = True

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given model instance."""
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

        # Minimize subcontext returndata
        for call in self.calls:
            for i in range(257):
                constraint = call.returndata.length == Uint256(i)
                if solver.check(constraint):
                    solver.add(constraint)
                    break

        for i in range(9):
            constraint = self.mystery_size == Uint256(0x123 >> i)
            if solver.check(constraint):
                solver.add(constraint)
                break

        solver.add(self.narrower)
        assert solver.check()

    def describe(self, solver: Solver) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        assert isinstance(self.pc, Termination)
        r: OrderedDict[str, str] = OrderedDict()
        returndata = self.pc.returndata.evaluate(solver)
        if returndata:
            r["Return"] = "0x" + returndata.hex()
        return r

    def compact_bytes(self, bytes: Bytes) -> Bytes:
        """Simplify the given bytes using the current constraints."""
        if bytes.reveal() is not None:
            return bytes

        solver = Solver()
        solver.add(self.constraint)
        assert solver.check()
        self.constraint &= bytes.compact(solver, Constraint(True))
        return bytes

    def compact_calldata(self, data: Bytes) -> Bytes | None:
        """Simplify the given bytes (optimized for calldata)."""
        solver = Solver()
        solver.add(self.constraint)
        if not solver.check():
            return None  # this path is unreachable

        length = solver.evaluate(data.length)
        constraint = data.length == Uint256(length)

        result: list[Uint8] = []
        for i in range(4):
            v = data[Uint256(i)]
            e = BYTES[solver.evaluate(v)]
            constraint &= v == e
            result.append(e)
        for i in range(4, length):
            result.append(data[Uint256(i)])

        if solver.check(~constraint):
            raise ValueError("expected concrete function signature and length")
        return Bytes(result[:length])  # remember, length can be < 4


@dataclass(frozen=True)
class Termination:
    """The result of running a contract to completion."""

    success: bool
    returndata: Bytes


@dataclass(frozen=True)
class Log:
    """A log entry emitted by the LOG* instruction."""

    data: Bytes
    topics: tuple[Uint256, ...]


@dataclass(frozen=True)
class Call:
    """Information about a CALL instruction."""

    transaction: Transaction
    ok: Constraint
    returndata: Bytes


@dataclass(frozen=True)
class DelegateCall(Call):
    """Information about a symbolic DELEGATECALL instruction."""

    previous_storage: Array[Uint256, Uint256]
    next_storage: Array[Uint256, Uint256]


@dataclass(frozen=True)
class GasHogCall(Call):
    """Represents a CALL to a proxy that consumes all available gas."""

    gas: Uint256


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

    states: tuple[State, ...]


@dataclass(frozen=True)
class Unreachable(ControlFlow):
    """Represents a state that is discovered to be unreachable."""

    pass
