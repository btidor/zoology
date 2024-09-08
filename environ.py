"""Types for modeling the execution environment."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Self

from bytes import BYTES, Bytes, Memory
from disassembler import Program, disassemble
from path import Path
from smt import (
    STARTING_HASHES,
    Array,
    Constraint,
    Solver,
    Substitutions,
    Uint8,
    Uint160,
    Uint256,
    concrete_hash,
    substitute,
)


@dataclass
class Blockchain:
    """Durable global state, persists across transactions."""

    contracts: dict[Address, Contract] = field(default_factory=dict)
    balances: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256](Uint256(0))
    )

    def transfer(self, tx: Transaction) -> Constraint:
        """Transfer value between accounts (checked)."""
        src, dst, value = tx.caller, tx.address, tx.callvalue

        ok = self.balances[src] >= value
        self.balances[src] -= value

        ok &= self.balances[dst] + value >= self.balances[dst]
        self.balances[dst] += value
        return ok


@dataclass
class Contract:
    """A contract account and its durable state."""

    program: Program

    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0))
    )
    nonce: int = 1  # starts at 1, see EIP-161


class Address(int):
    """A concrete contract address."""

    @classmethod
    def unwrap(cls, address: Uint160, op: str = "operation") -> Self:
        """Convert a Uint160 to an Address."""
        v = address.reveal()
        if v is None:
            raise ValueError(f"{op} requires concrete address")
        return cls(v)


@dataclass(frozen=True)
class Block:
    """A block in the blockchain."""

    number: Uint256 = Uint256(16030969)
    coinbase: Uint160 = Uint160(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5)
    timestamp: Uint256 = Uint256(1669214471)
    prevrandao: Uint256 = Uint256(
        0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
    )
    gaslimit: Uint256 = Uint256(30000000000000000)
    chainid: Uint256 = Uint256(1)
    basefee: Uint256 = Uint256(12267131109)

    # Map from offset -> blockhash for the last 256 complete blocks. The most
    # recent block has offset 255.
    hashes: Array[Uint8, Uint256] = field(
        default_factory=lambda: Block._concrete_hashes()
    )

    @classmethod
    def _concrete_hashes(cls) -> Array[Uint8, Uint256]:
        hashes = Array[Uint8, Uint256](Uint256(0))
        for n, hash in enumerate(STARTING_HASHES):
            hashes[BYTES[n]] = hash
        return hashes

    def successor(self) -> Block:
        """Produce a plausible next block."""
        hashes = Array[Uint8, Uint256](Uint256(0))
        assert (start := self.hashes[Uint8(0)].reveal()) is not None
        hashes[Uint8(0)] = concrete_hash(start.to_bytes(32))
        for i in range(1, 256):
            hashes[Uint8(i)] = self.hashes[Uint8(i - 1)]

        return Block(
            number=self.number + Uint256(1),
            coinbase=self.coinbase,
            timestamp=self.timestamp + Uint256(12),
            prevrandao=self.prevrandao * Uint256(2147483647),
            gaslimit=self.gaslimit,
            chainid=self.chainid,
            basefee=self.basefee,
            hashes=hashes,
        )


@dataclass(frozen=True)
class Transaction:
    """A contract call."""

    origin: Uint160 = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
    caller: Uint160 = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    address: Uint160 = Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
    callvalue: Uint256 = Uint256(0)
    calldata: Bytes = Bytes()
    gasprice: Uint256 = Uint256(0x12)

    def narrow(self, solver: Solver) -> None:
        """Apply soft constraints to a given solver instance."""
        # Minimize calldata length
        for i in range(257):
            constraint = self.calldata.length == Uint256(i)
            if solver.check(constraint):
                solver.add(constraint)
                break

        # Minimize callvalue
        for i in range(257):
            constraint = self.callvalue == Uint256(2**i - 1)
            if solver.check(constraint):
                solver.add(constraint)
                break

        # Prefer non-proxied calls
        constraint = self.caller == self.origin
        if solver.check(constraint):
            solver.add(constraint)

        assert solver.check()


@dataclass
class Runtime:
    """
    Transient state for a transaction execution.

    Runtime encapsulates state that's discarded after the contract finishes
    executing, like the program counter, the stack, and memory. It's used by
    `ops.py` to express how operations mutate state.

    Global state like contracts and balances is kept on a separate Blockchain
    object. This separation allows the abstract compiler to produce a compact,
    general representation of contract behavior that can be cached and reused.

    Runtimes are sortable, with shorter paths before longer ones.
    """

    program: Program = field(default=disassemble(Bytes()))
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0))
    )

    path: Path = field(default_factory=Path)

    pc: int = 0
    stack: list[Uint256] = field(default_factory=list)
    memory: Memory = field(default_factory=Memory)
    latest_return: Bytes = Bytes()

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, Runtime):
            return NotImplemented
        return self.path.id < other.path.id

    def __eq__(self, other: Any) -> bool:
        return id(self) == id(other)

    def push(self, value: Uint256) -> None:
        """Push a value onto the stack, checking for overflow."""
        self.stack.append(value)
        if len(self.stack) > 1024:
            raise RuntimeError("evm stack overflow")

    def substitute(self, subs: Substitutions) -> Self:
        """
        Perform term substitution.

        If any SHA3 hashes become concrete, term substitution will be
        recursively re-applied until no more hashes can be resolved.
        """
        term = substitute(self, subs)
        while extra := term.path.update_substitutions():
            term = substitute(term, extra)
        return term
