"""Classes for modeling contract execution."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Iterable, Self

from bytes import Bytes, Memory
from disassembler import Program
from environment import Block, Contract, Transaction
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


@dataclass(slots=True)
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str = ""

    block: Block = field(default_factory=Block)
    transaction: Transaction = field(default_factory=Transaction)
    sha3: SHA3 = field(default_factory=SHA3)

    # ASSUMPTION: all contract accounts are listed here. All other addresses are
    # either EOAs or are uncreated.
    contracts: dict[int, Contract] = field(
        default_factory=dict[int, Contract]
    )  # address -> Contract
    balances: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256](Uint256(0))
    )

    pc: int | Termination = 0
    stack: list[Uint256] = field(default_factory=list[Uint256])
    memory: Memory = field(default_factory=Memory)
    logs: list[Log] = field(default_factory=list[Any])

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
    #
    # ASSUMPTION: the mystery proxy resides at a fixed, concrete address.
    #
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

    # Tracks the symbolic constraints that must be satisfied in order for the
    # program to reach this state. Largely based on the JUMPI instructions (if
    # statements) encountered in the execution.
    solver: Solver = field(default_factory=Solver)

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    # These variables help the search avoid getting stuck in infinite loops by
    # prioritizing states according to a cost function.
    cost: int = 0
    last_jumpi: int = -1
    trace: list[str] = field(default_factory=list[str])

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
        self.solver.add(self.block.number >= Uint256(256))
        if self.mystery_proxy is not None:
            assert self.mystery_proxy.reveal() is not None, (
                "State requires concrete mystery proxy address, if present"
            )

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, State):
            return NotImplemented
        return self.cost < other.cost

    @property
    def program(self) -> Program:
        """Return the currently-executing program."""
        if self.program_override is not None:
            return self.program_override
        assert (address := self.transaction.address.reveal()) is not None
        return self.contracts[address].program

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
            contract = Contract(program=contract)
        assert (address := contract.address.reveal()) is not None
        if self.mystery_proxy is not None and address == self.mystery_proxy.reveal():
            raise KeyError(
                f"Contract 0x{address.to_bytes(20).hex()} shadows mystery proxy"
            )
        if address in self.contracts and not overwrite:
            raise KeyError(f"Contract 0x{address.to_bytes(20).hex()} already exists")
        self.contracts[address] = contract
        return self

    def transfer(self, src: Uint160, dst: Uint160, val: Uint256) -> None:
        """Transfer value from one account to another."""
        if val.reveal() == 0:
            return
        elif self.changed is None:
            raise ValueError("Nonzero transfer is forbidden during a STATICCALL")

        # ASSUMPTION: if `balances[src]` drops below zero, execution will
        # revert. Therefore, `balances[src] >= val`.
        self.solver.add(underflow_safe(self.balances[src], val))
        # ASSUMPTION: there isn't enough ETH in existence to overflow an
        # account's balance; all balances are less than 2^255 wei.
        self.solver.add(overflow_safe(self.balances[dst], val))

        self.balances[src] -= val
        self.balances[dst] += val
        self.changed = True

    def hash(self, input: Bytes) -> Uint256:
        """
        Compute the SHA3 hash of a given key.

        Automatically adds hash constraints to the current constraint.
        """
        digest, constraint = self.sha3.hash(input)
        self.solver.add(constraint)
        return digest

    def cleanup(self) -> None:
        """Perform deferred cleanup from SELFDESTRUCT operations."""
        for key, contract in list(self.contracts.items()):
            if contract.destructed:
                del self.contracts[key]

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

        # Minimize subcontext returndata/calldata
        for call in self.calls:
            call.narrow(solver)

        assert solver.check()


@dataclass(frozen=True, slots=True)
class Termination:
    """The result of running a contract to completion."""

    success: bool
    returndata: Bytes

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self


@dataclass(frozen=True, slots=True)
class Log:
    """A log entry emitted by the LOG* instruction."""

    data: Bytes
    topics: tuple[Uint256, ...]

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self


@dataclass(frozen=True, slots=True)
class Call:
    """Information about a CALL instruction."""

    transaction: Transaction
    ok: Constraint
    returndata: Bytes
    subcalls: tuple[Call, ...]

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given solver instance."""
        if self.returndata.length.reveal() is None:
            for i in range(257):
                constraint = self.returndata.length == Uint256(i)
                if solver.check(constraint):
                    solver.add(constraint)
                    break
        if self.transaction.calldata.length.reveal() is None:
            for i in range(257):
                constraint = self.transaction.calldata.length == Uint256(i)
                if solver.check(constraint):
                    solver.add(constraint)
                    break
        for call in self.subcalls:
            call.narrow(solver)

    def describe(
        self, solver: Solver, select_: Uint160, /, *, prints: bool = False
    ) -> Iterable[str]:
        """Yield a human-readable description of the Call."""
        address = solver.evaluate(self.transaction.address)
        assert (select := select_.reveal()) is not None
        prints = prints or address == select

        if prints:
            if address == select:
                yield " -> Proxy CALL "
            else:
                yield f" -> To 0x{address.to_bytes(20).hex()}:\n"
                yield "    CALL "
            yield from self.transaction.calldata.describe(solver)
            value = solver.evaluate(self.transaction.callvalue)
            if value:
                yield f"\tvalue: {value}"
            yield "\n"

        for call in self.subcalls:
            first = True
            for line in call.describe(solver, select_, prints=prints):
                if prints:
                    if first:
                        yield "    "
                        first = False
                    line = line.replace("\n", "\n    ")
                    if line.endswith("\n    "):
                        line = line[:-4]
                        first = True
                    yield line
                else:
                    yield line

        if prints:
            ok = solver.evaluate(self.ok)
            yield f"    {'RETURN' if ok else 'REVERT'} "
            yield from self.returndata.describe(solver, prefix=0)
            yield "\n"


@dataclass(frozen=True, slots=True)
class DelegateCall(Call):
    """Information about a symbolic DELEGATECALL instruction."""

    previous_storage: Array[Uint256, Uint256]
    next_storage: Array[Uint256, Uint256] | None  # None if SELFDESTRUCTed

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def describe(
        self, solver: Solver, select_: Uint160, /, *, prints: bool = False
    ) -> Iterable[str]:
        """Yield a human-readable description of the Call."""
        yield " -> Proxy DELEGATECALL "
        yield from self.transaction.calldata.describe(solver)
        value = solver.evaluate(self.transaction.callvalue)
        if value:
            yield f"\tvalue: {value}"
        yield "\n"
        assert not self.subcalls

        if self.next_storage is None:
            yield "    SELFDESTRUCT\n"
        else:
            ok = solver.evaluate(self.ok)
            yield f"    {'RETURN' if ok else 'REVERT'} "
            yield from self.returndata.describe(solver, prefix=0)
            yield "\n"
            if ok:
                prev = solver.evaluate(self.previous_storage)
                for k, v in solver.evaluate(self.next_storage).items():
                    if prev[k] != v:
                        yield f"      {hex(k)} -> {hex(v)}\n"


@dataclass(frozen=True, slots=True)
class GasHogCall(Call):
    """Represents a CALL to a proxy that consumes all available gas."""

    gas: Uint256

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def describe(
        self, solver: Solver, select_: Uint160, /, *, prints: bool = False
    ) -> Iterable[str]:
        """Yield a human-readable description of the Call."""
        yield " -> Proxy CALL "
        yield from self.transaction.calldata.describe(solver)
        value = solver.evaluate(self.transaction.callvalue)
        if value:
            yield f"\tvalue: {value}"
        yield "\n"
        assert not self.subcalls
        yield "    CONSUME ALL GAS\n"


type ControlFlow = Jump | Descend | Unreachable


@dataclass(frozen=True, slots=True)
class Jump:
    """A JUMPI instruction that branches the control flow."""

    targets: tuple[State, ...]

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self


@dataclass(frozen=True, slots=True)
class Descend:
    """A CALL, DELEGATECALL, etc. instruction."""

    states: tuple[State, ...]

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self


@dataclass(frozen=True, slots=True)
class Unreachable:
    """Represents a state that is discovered to be unreachable."""

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self
