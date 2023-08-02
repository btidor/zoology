"""Classes for modeling the state of the Ethereum blockchain."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass, field

from disassembler import Program, disassemble
from smt.arrays import Array
from smt.bytes import FrozenBytes
from smt.sha3 import concrete_hash
from smt.smt import BitVector, Uint8, Uint160, Uint256
from smt.solver import Solver


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
            chainid=Uint256(f"CHAINID"),
            basefee=Uint256(f"BASEFEE{suffix}"),
            hashes=Array.symbolic(f"BLOCKHASH{suffix}", Uint8, Uint256),
        )

    @classmethod
    def __concrete_hashes(cls) -> Array[Uint8, Uint256]:
        hashes = Array.concrete(Uint8, Uint256(0))
        hashes[Uint8(255)] = Uint256(
            0xF798B79831B745F4F756FBD50CFEBAE9FE8AF348CB8EF47F739939142EC9D1E0
        )
        for i in range(254, -1, -1):
            hashes[Uint8(i)] = concrete_hash(hashes[Uint8(i + 1)].unwrap(bytes))
        return hashes

    def successor(self) -> Block:
        """Produce a plausible next block."""
        hashes = Array.concrete(Uint8, Uint256(0))
        hashes[Uint8(0)] = concrete_hash(self.hashes[Uint8(0)].unwrap(bytes))
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
    program: Program = disassemble(b"")
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array.concrete(Uint256, Uint256(0))
    )
    nonce: Uint256 = Uint256(1)  # starts at 1, see EIP-161


@dataclass(frozen=True)
class Transaction:
    """The inputs to a contract call."""

    origin: Uint160 = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
    caller: Uint160 = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
    callvalue: Uint256 = Uint256(0)
    calldata: FrozenBytes = FrozenBytes.concrete()
    gasprice: Uint256 = Uint256(0x12)

    @classmethod
    def symbolic(
        cls, suffix: str, origin: Uint160 | None = None, caller: Uint160 | None = None
    ) -> Transaction:
        """Create a fully-symbolic Transaction."""
        return Transaction(
            origin=Uint160(f"ORIGIN{suffix}") if origin is None else origin,
            caller=Uint160(f"CALLER{suffix}") if caller is None else caller,
            callvalue=Uint256(f"CALLVALUE{suffix}"),
            calldata=FrozenBytes.symbolic(f"CALLDATA{suffix}"),
            gasprice=Uint256(f"GASPRICE{suffix}"),
        )

    def describe(self, solver: Solver) -> OrderedDict[str, str]:
        """
        Use a model to evaluate this instance as a dictionary of attributes.

        Only attributes present in the model will be included.
        """
        r: OrderedDict[str, BitVector | str | None] = OrderedDict()
        calldata = self.calldata.describe(solver)
        r["Data"] = f"0x{calldata[:8]} {calldata[8:]}".strip() if calldata else None
        r["Value"] = self.callvalue
        r["Caller"] = self.caller
        r["Gas"] = self.gasprice

        s: OrderedDict[str, str] = OrderedDict()
        for k in list(r.keys()):
            match (v := r[k]):
                case None:
                    pass
                case BitVector():
                    if v.maybe_unwrap():
                        s[k] = "0x" + v.unwrap(bytes).hex()
                    else:
                        v = solver.evaluate(v)
                        if v.maybe_unwrap():
                            s[k] = "0x" + v.unwrap(bytes).hex()
                case str():
                    s[k] = v
        return s


@dataclass
class Universe:
    """The state of the entire blockchain and our interactions with it."""

    suffix: str = ""

    balances: Array[Uint160, Uint256] = field(
        # address -> balance in wei
        default_factory=lambda: Array.concrete(Uint160, Uint256(0))
    )

    contracts: dict[int, Contract] = field(default_factory=dict)  # address -> Contract
    codesizes: Array[Uint160, Uint256] = field(
        # address -> code size
        default_factory=lambda: Array.concrete(Uint160, Uint256(0))
    )

    @classmethod
    def symbolic(cls, suffix: str) -> Universe:
        """Create a fully-symbolic Universe."""
        return Universe(
            suffix=suffix,
            balances=Array.symbolic(f"BALANCE{suffix}", Uint160, Uint256),
            contracts={},
            codesizes=Array.symbolic(f"CODESIZE{suffix}", Uint160, Uint256),
        )

    def add_contract(self, contract: Contract) -> None:
        """
        Add a contract to the contract registry.

        The contract must have a concrete address.
        """
        self.contracts[contract.address.unwrap()] = contract
        self.codesizes[contract.address] = contract.program.code.length
