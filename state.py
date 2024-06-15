"""Types for modeling the execution environment."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, NewType

from bytes import BYTES, Bytes, Memory
from disassembler import Program, disassemble
from path import Path, concrete_hash
from smt import (
    Array,
    Solver,
    Substitutable,
    Uint8,
    Uint160,
    Uint256,
)


@dataclass
class Blockchain:
    """Durable global state, persists across transactions."""

    contracts: Contracts = field(default_factory=dict)
    balance: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256](Uint256(0))
    )


@dataclass
class Contract:
    """A contract account and its durable state."""

    program: Program

    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0))
    )
    nonce: Uint256 = Uint256(1)  # starts at 1, see EIP-161


Address = NewType("Address", int)  # a concrete contract address
Contracts = dict[Address, Contract]


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
        for n in range(256):
            hashes[BYTES[n]] = concrete_hash((n).to_bytes())
        return hashes


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
        """Apply soft  constraints to a given solver instance."""
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
        assert solver.check()


@dataclass
class Runtime:
    """Transient state for a transaction execution."""

    program: Program = field(default=disassemble(Bytes()))
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0))
    )

    path: Path = field(default_factory=Path)

    pc: int = 0
    stack: list[Uint256] = field(default_factory=list)
    memory: Memory = field(default_factory=Memory)

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, Runtime):
            return NotImplemented
        return self.path.id < other.path.id


@dataclass(frozen=True)
class Terminus(Substitutable):
    """The result of running a contract to completion."""

    path: Path

    success: bool
    returndata: Bytes

    storage: Array[Uint256, Uint256] | None  # unset if static or reverted
