"""Classes for modeling the state of the Ethereum blockchain."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass, field

from disassembler import Program, disassemble
from smt.arrays import Array
from smt.bytes import FrozenBytes
from smt.smt import BitVector, Constraint, Uint160, Uint256
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
        )


@dataclass
class Contract:
    """A deployed contract account with code and symbolic storage."""

    address: Uint160 = Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
    program: Program = disassemble(b"")
    storage: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array.concrete(Uint256, Uint256(0))
    )


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
    transfer_constraints: list[Constraint] = field(default_factory=list)

    contracts: dict[int, Contract] = field(default_factory=dict)  # address -> Contract
    codesizes: Array[Uint160, Uint256] = field(
        # address -> code size
        default_factory=lambda: Array.concrete(Uint160, Uint256(0))
    )
    blockhashes: Array[Uint256, Uint256] = field(
        default_factory=lambda: Array.concrete(Uint256, Uint256(0))
    )

    # These variables track how much value has been moved from the contracts
    # under test to our agent's accounts. To avoid overflow errors, we track
    # value contributed to and value extracted from the contracts under test as
    # two separate unsigned (nonnegative) integers.
    agents: list[Uint160] = field(default_factory=list)
    contribution: Uint256 = Uint256(0)
    extraction: Uint256 = Uint256(0)

    @classmethod
    def symbolic(cls, suffix: str) -> Universe:
        """Create a fully-symbolic Universe."""
        return Universe(
            suffix=suffix,
            balances=Array.symbolic(f"BALANCE{suffix}", Uint160, Uint256),
            transfer_constraints=[],
            contracts={},
            codesizes=Array.symbolic(f"CODESIZE{suffix}", Uint160, Uint256),
            blockhashes=Array.symbolic(f"BLOCKHASH{suffix}", Uint256, Uint256),
            agents=[],
            contribution=Uint256(f"CONTRIBUTION{suffix}"),
            extraction=Uint256(f"EXTRACTION{suffix}"),
        )

    def add_contract(self, contract: Contract) -> None:
        """
        Add a contract to the contract registry.

        The contract must have a concrete address.
        """
        self.contracts[contract.address.unwrap()] = contract
        self.codesizes[contract.address] = contract.program.code.length

    def transfer(self, src: Uint160, dst: Uint160, val: Uint256) -> None:
        """Transfer value from one account to another."""
        # ASSUMPTION: If `balances[src]` drops below zero, execution will
        # revert. Therefore, `balances[src] >= val`.
        self.transfer_constraints.append(
            Uint256.underflow_safe(self.balances[src], val)
        )
        self.balances[src] -= val

        # ASSUMPTION: There isn't enough ETH in existence to overflow an
        # account's balance; all balances are less than 2^255 wei.
        self.transfer_constraints.append(Uint256.overflow_safe(self.balances[dst], val))
        self.balances[dst] += val

        de = Constraint.any(*[dst == agent for agent in self.agents]).ite(
            val, Uint256(0)
        )
        self.transfer_constraints.append(Uint256.overflow_safe(self.extraction, de))
        self.extraction += de

        dc = Constraint.any(*[src == agent for agent in self.agents]).ite(
            val, Uint256(0)
        )
        self.transfer_constraints.append(Uint256.overflow_safe(self.contribution, dc))
        self.contribution += dc

    def constrain(self, solver: Solver) -> None:
        """Apply accumulated constraints to the given solver instance."""
        for _, constraint in enumerate(self.transfer_constraints):
            solver.assert_and_track(constraint)
