"""Classes for modeling the state of the Ethereum blockchain."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List

import z3

from disassembler import Program
from symbolic import BW, Array, Constraint, uint160, uint256


@dataclass
class Block:
    """A block in the blockchain."""

    number: uint256
    coinbase: uint160
    timestamp: uint256
    prevrandao: uint256
    gaslimit: uint256
    chainid: uint256
    basefee: uint256


@dataclass
class Contract:
    """A deployed contract account with code and symbolic storage."""

    program: Program
    storage: Array

    def copy(self) -> Contract:
        """Return a deep copy of this instance."""
        return Contract(
            program=self.program,
            storage=self.storage.copy(),
        )


@dataclass
class Universe:
    """The state of the entire blockchain and our interactions with it."""

    suffix: str

    balances: Array
    transfer_constraints: List[Constraint]

    # These variables track how much value has been moved from the contracts
    # under test to our agent's accounts. To avoid overflow errors, we track
    # value contributed to and value extracted from the contracts under test as
    # two separate unsigned (nonnegative) integers.
    agents: List[uint160]
    contribution: uint256
    extraction: uint256

    def transfer(self, src: uint160, dst: uint160, val: uint256) -> None:
        """Transfer value from one account to another."""
        self.transfer_constraints.append(
            # If `balances[src]` drops below zero, execution will revert.
            # Therefore, `balances[src] >= 0`.
            z3.BVSubNoUnderflow(self.balances[src], val, False)
        )
        self.transfer_constraints.append(
            # There isn't enough ETH in existence to overflow an account's
            # balance.
            z3.BVAddNoOverflow(self.balances[dst], val, False)
        )
        self.balances[src] -= val
        self.balances[dst] += val

        ext = z3.If(z3.Or(False, *[dst == agent for agent in self.agents]), val, BW(0))
        self.transfer_constraints.append(
            z3.BVAddNoOverflow(self.extraction, ext, False)
        )
        self.extraction += ext
        cont = z3.If(z3.Or(False, *[src == agent for agent in self.agents]), val, BW(0))
        self.transfer_constraints.append(
            z3.BVAddNoOverflow(self.contribution, cont, False)
        )
        self.contribution += cont

    def constrain(self, solver: z3.Optimize) -> None:
        """Apply accumulated constraints to the given solver instance."""
        for i, constraint in enumerate(self.transfer_constraints):
            solver.assert_and_track(constraint, f"XFER{i}{self.suffix}")

    def copy(self) -> Universe:
        """Return a deep copy of this instance."""
        return Universe(
            suffix=self.suffix,
            balances=self.balances.copy(),
            transfer_constraints=self.transfer_constraints.copy(),
            agents=self.agents.copy(),
            contribution=self.contribution,
            extraction=self.extraction,
        )