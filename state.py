"""Types for modeling the execution environment."""

from __future__ import annotations

import abc
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Self, TypeVar

from bytes import BYTES, Bytes, Memory
from disassembler import Program, disassemble
from sha3 import SHA3, concrete_hash
from smt import (
    Array,
    Constraint,
    Solver,
    Substitutions,
    Uint8,
    Uint160,
    Uint256,
    substitute,
)


@dataclass(frozen=True)
class Termination:
    """The result of running a contract to completion."""

    success: bool
    returndata: Bytes

    def __substitute__(self, subs: Substitutions) -> Self:
        return _substitute(self, subs)


@dataclass(frozen=True)
class Transaction:
    """The inputs to a contract call."""

    origin: Uint160 = field(
        default_factory=lambda: Uint160("ORIGIN"),
    )
    caller: Uint160 = field(
        default_factory=lambda: Uint160("CALLER"),
    )
    address: Uint160 = field(
        default_factory=lambda: Uint160("ADDRESS"),
    )
    callvalue: Uint256 = field(
        default_factory=lambda: Uint256("CALLVALUE"),
    )
    calldata: Bytes = field(
        default_factory=lambda: Bytes.symbolic("CALLDATA"),
    )
    gasprice: Uint256 = field(
        default_factory=lambda: Uint256("GASPRICE"),
    )

    def __substitute__(self, subs: Substitutions) -> Self:
        return _substitute(self, subs)


@dataclass(frozen=True)
class Block:
    """A block in the blockchain."""

    number: Uint256 = field(
        default_factory=lambda: Uint256("NUMBER"),
    )
    coinbase: Uint160 = field(
        default_factory=lambda: Uint160("COINBASE"),
    )
    timestamp: Uint256 = field(
        default_factory=lambda: Uint256("TIMESTAMP"),
    )
    prevrandao: Uint256 = field(
        default_factory=lambda: Uint256("PREVRANDAO"),
    )
    gaslimit: Uint256 = field(
        default_factory=lambda: Uint256("GASLIMIT"),
    )
    chainid: Uint256 = field(
        default_factory=lambda: Uint256("CHAINID"),
    )
    basefee: Uint256 = field(
        default_factory=lambda: Uint256("BASEFEE"),
    )

    # Map from offset -> blockhash for the last 256 complete blocks. The most
    # recent block has offset 255.
    hashes: Array[Uint8, Uint256] = field(
        default_factory=lambda: Array[Uint8, Uint256]("BLOCKHASH")
    )

    @classmethod
    def sample(cls, i: int) -> Block:
        """Return a plausible block with concrete values."""
        hashes = Array[Uint8, Uint256](Uint256(0))
        for n in range(256):
            hashes[BYTES[n]] = concrete_hash((n + i).to_bytes())

        return Block(
            number=Uint256(16030969 + i),
            coinbase=Uint160(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5),
            timestamp=Uint256(1669214471 + 12 * i),
            prevrandao=Uint256(
                0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
            )
            * Uint256(2147483647 ^ i),
            gaslimit=Uint256(30000000000000000),
            chainid=Uint256(1),
            basefee=Uint256(12267131109),
            hashes=hashes,
        )

    def __substitute__(self, subs: Substitutions) -> Self:
        return _substitute(self, subs)


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    block: Block = field(default_factory=Block)
    transaction: Transaction = field(default_factory=Transaction)
    sha3: SHA3 = field(default_factory=SHA3)

    program: Program = field(default=disassemble(Bytes()))
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256]("STORAGE")
    )

    balance: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256]("BALANCE")
    )

    pc: int | Termination = 0
    stack: list[Uint256] = field(default_factory=list)
    memory: Memory = field(default_factory=Memory)

    # The return data of the most recent subcontext, for the RETURNDATASIZE and
    # RETURNDATACOPY instructions.
    latest_return: Bytes = Bytes()

    # Symbolic constraint that must be satisfied in order for the program to
    # reach this state. Largely based on the JUMPI instructions (if statements)
    # encountered in the execution.
    constraint: Constraint = field(default=Constraint(True))

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    # Tracks the number of times each JUMPI instruction has been reached. States
    # are prioritized by their cost, which is computed as the sum of the branch
    # counts, exponentially weighted to penalize long or infinite loops.
    branching: dict[int, int] = field(default_factory=lambda: defaultdict(lambda: 0))
    cost: int = 0

    # Whether the path is legal to execute during a STATICCALL.
    static: bool = True

    # TODO: document me!
    callouts: list[Callout] = field(default_factory=list)

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, State):
            return NotImplemented
        return self.cost < other.cost

    def px(self) -> str:
        """Return a human-readable version of the path."""
        return "Px" + hex(self.path)[2:].upper()

    # TODO: the current block number is at least 256. This prevents the
    # BLOCKHASH instruction from overflowing.
    # self.constraint &= self.block.number >= Uint256(256)

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given model instance."""
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

        assert solver.check()

    def __substitute__(self, subs: Substitutions) -> Self:
        return _substitute(self, subs)


S = TypeVar("S", bound=Termination | Block | Transaction | State)


def _substitute(item: S, subs: Substitutions) -> S:
    args = dict[str, Any]()
    for key in item.__dataclass_fields__.keys():
        value = getattr(item, key)
        args[key] = substitute(value, subs)
    return item.__class__(**args)


@dataclass
class Contract:
    """A deployed contract account."""

    address: Uint160
    program: Program

    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0))
    )
    nonce: Uint256 = Uint256(1)  # starts at 1, see EIP-161

    invisible: bool = False  # can't be CALLed during analysis

    @property
    def codesize(self) -> Uint256:
        """Return the size of the code, in bytes."""
        return self.program.code.length

    def __post_init__(self) -> None:
        assert self.address.reveal() is not None, "Contract requires concrete address"


class Callout(abc.ABC):
    """TODO."""

    pass


@dataclass
class CreateCallout(Callout):
    """TODO."""

    initcode: Bytes
    value: Uint256

    success: Constraint
