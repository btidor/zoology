"""Classes for modeling the state of the Ethereum blockchain."""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass

from disassembler import Program
from smt.arrays import Array
from smt.bytes import FrozenBytes
from smt.smt import BitVector, Constraint, Uint160, Uint256
from smt.solver import Solver


@dataclass(frozen=True)
class Block:
    """A block in the blockchain."""

    number: Uint256
    coinbase: Uint160
    timestamp: Uint256
    prevrandao: Uint256
    gaslimit: Uint256
    chainid: Uint256
    basefee: Uint256


@dataclass
class Contract:
    """A deployed contract account with code and symbolic storage."""

    address: Uint160
    program: Program
    storage: Array[Uint256, Uint256]


@dataclass(frozen=True)
class Transaction:
    """The inputs to a contract call."""

    origin: Uint160
    caller: Uint160
    callvalue: Uint256
    calldata: FrozenBytes
    gasprice: Uint256

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

    suffix: str

    balances: Array[Uint160, Uint256]  # address -> balance in wei
    transfer_constraints: list[Constraint]

    contracts: dict[int, Contract]  # address -> Contract
    codesizes: Array[Uint160, Uint256]  # address -> code size

    blockhashes: Array[Uint256, Uint256]

    # These variables track how much value has been moved from the contracts
    # under test to our agent's accounts. To avoid overflow errors, we track
    # value contributed to and value extracted from the contracts under test as
    # two separate unsigned (nonnegative) integers.
    agents: list[Uint160]
    contribution: Uint256
    extraction: Uint256

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
