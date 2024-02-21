"""Classes for modeling the state of the Ethereum blockchain."""

from __future__ import annotations

import copy
from collections import OrderedDict
from dataclasses import dataclass, field
from typing import Any

from bytes import Bytes
from disassembler import Program, disassemble
from sha3 import concrete_hash
from smt import Array, Int, Solver, Uint, Uint8, Uint160, Uint256


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
        default_factory=lambda: Block.__concrete_hashes()
    )

    @classmethod
    def symbolic(cls, suffix: str) -> Block:
        """Create a fully-symbolic Block."""
        return Block(
            number=Uint256(f"NUMBER{suffix}"),
            coinbase=Uint160(f"COINBASE{suffix}"),
            timestamp=Uint256(f"TIMESTAMP{suffix}"),
            prevrandao=Uint256(f"PREVRANDAO{suffix}"),
            gaslimit=Uint256(f"GASLIMIT{suffix}"),
            chainid=Uint256("CHAINID"),
            basefee=Uint256(f"BASEFEE{suffix}"),
            hashes=Array[Uint8, Uint256](f"BLOCKHASH{suffix}"),
        )

    @classmethod
    def __concrete_hashes(cls) -> Array[Uint8, Uint256]:
        hashes = Array[Uint8, Uint256](Uint256(0))
        hashes[Uint8(255)] = Uint256(
            0xF798B79831B745F4F756FBD50CFEBAE9FE8AF348CB8EF47F739939142EC9D1E0
        )
        for i in range(254, -1, -1):
            assert (prev := hashes[Uint8(i + 1)].reveal()) is not None
            hashes[Uint8(i)] = concrete_hash(prev.to_bytes(32))
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


@dataclass
class Contract:
    """A deployed contract account with code and symbolic storage."""

    address: Uint160 = Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
    program: Program = disassemble(Bytes())
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array[Uint256, Uint256](Uint256(0)),
    )
    nonce: Uint256 = Uint256(1)  # starts at 1, see EIP-161

    def clone_and_reset(self) -> Contract:
        """Clone this Contract and reset array access tracking."""
        result = copy.copy(self)
        result.storage = result.storage.clone_and_reset()
        return result

    def __post_init__(self) -> None:
        assert self.address.reveal() is not None, "Contract requires concrete address"


@dataclass(frozen=True)
class Transaction:
    """The inputs to a contract call."""

    origin: Uint160 = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
    caller: Uint160 = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    address: Uint160 = Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
    callvalue: Uint256 = Uint256(0)
    calldata: Bytes = Bytes()
    gasprice: Uint256 = Uint256(0x12)

    def __post_init__(self) -> None:
        assert self.address.reveal() is not None, "Contract requires concrete address"

    def describe(self, solver: Solver) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        r: OrderedDict[str, Uint[Any] | Int[Any] | str | None] = OrderedDict()
        calldata = self.calldata.evaluate(solver).hex()
        r["Data"] = f"0x{calldata[:8]} {calldata[8:]}".strip() if calldata else None
        r["Value"] = self.callvalue
        r["Caller"] = self.caller
        r["Gas"] = self.gasprice

        s: OrderedDict[str, str] = OrderedDict()
        for k in list(r.keys()):
            match v := r[k]:
                case None:
                    pass
                case Uint() | Int():
                    b = solver.evaluate(v)
                    if b > 0:
                        s[k] = "0x" + b.to_bytes(v.width // 8).hex()
                case str():
                    s[k] = v
        return s


@dataclass
class Universe:
    """The state of the entire blockchain and our interactions with it."""

    suffix: str = ""

    balances: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array[Uint160, Uint256](Uint256(0))
    )

    # ASSUMPTION: all contract accounts are listed here. All other addresses are
    # either EOAs or are uncreated.
    contracts: dict[int, Contract] = field(default_factory=dict)  # address -> Contract

    @classmethod
    def symbolic(cls, suffix: str) -> Universe:
        """Create a fully-symbolic Universe."""
        return Universe(
            suffix=suffix,
            balances=Array[Uint160, Uint256](f"BALANCE{suffix}"),
        )

    def with_contract(
        self, contract: Contract | Program, overwrite: bool = False
    ) -> Universe:
        """
        Add a contract to the contract registry.

        The contract must have a concrete address.
        """
        if isinstance(contract, Program):
            contract = Contract(program=contract)
        assert (address := contract.address.reveal()) is not None
        if address in self.contracts and not overwrite:
            raise KeyError(f"Contract 0x{address.to_bytes(20).hex()} already exists")
        self.contracts[address] = contract
        return self

    def clone_and_reset(self) -> Universe:
        """Clone this Universe and reset array access tracking."""
        return Universe(
            suffix=self.suffix,
            balances=self.balances.clone_and_reset(),
            contracts={k: v.clone_and_reset() for (k, v) in self.contracts.items()},
        )
