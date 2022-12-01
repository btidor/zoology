from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, cast

import z3

from _hash import SHA3
from _symbolic import (
    BA,
    BW,
    ByteArray,
    Constraint,
    IntrospectableArray,
    do_check,
    uint8,
    uint160,
    uint256,
)
from disassembler import Program


def constrain_to_goal(solver: z3.Optimize, start: Universe, end: Universe) -> None:
    solver.assert_and_track(z3.ULT(start.extraction, start.contribution), "GOAL.PRE")
    solver.assert_and_track(z3.UGT(end.extraction, end.contribution), "GOAL.POST")


@dataclass
class Block:
    """A block in the Ethereum blockchain."""

    number: uint256 = BW(16030969)
    coinbase: uint160 = BA(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5)
    timestamp: uint256 = BW(1669214471)
    prevrandao: uint256 = BW(
        0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
    )
    gaslimit: uint256 = BW(30000000000000000)
    chainid: uint256 = BW(1)
    basefee: uint256 = BW(12267131109)


@dataclass
class Contract:
    """A deployed contract account with code and symbolic storage."""

    program: Program
    storage: IntrospectableArray = IntrospectableArray(
        "STORAGE", z3.BitVecSort(256), BW(0)
    )


@dataclass
class Universe:
    """The state of the entire blockchain and our interactions with it."""

    suffix: str = ""

    balances: IntrospectableArray = IntrospectableArray(
        "BALANCES", z3.BitVecSort(160), BW(0)
    )
    transfer_constraints: List[Constraint] = field(default_factory=list)

    # These variables track how much value has been moved from the contracts
    # under test to our agent's accounts. To avoid overflow errors, we track
    # value contributed to and value extracted from the contracts under test as
    # two separate unsigned (nonnegative) integers.
    agents: List[uint160] = field(default_factory=list)
    contribution: uint256 = BW(0)
    extraction: uint256 = BW(0)

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
        self.extraction += cont

    def constrain(self, solver: z3.Optimize) -> None:
        """Apply accumulated constraints to the given solver instance."""
        for i, constraint in enumerate(self.transfer_constraints):
            solver.assert_and_track(constraint, f"XFER{i}{self.suffix}")


@dataclass
class State:
    """Transient context state associated with a contract invocation."""

    suffix: str = ""

    sha3: SHA3 = field(default_factory=SHA3)

    pc: int = 0
    stack: List[uint256] = field(default_factory=list)
    memory: Dict[int, uint8] = field(
        default_factory=dict
    )  # concrete index -> 1-byte value

    address: uint160 = BA(0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    origin: uint160 = BA(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    caller: uint160 = BA(0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC)
    callvalue: uint256 = BW(0)
    calldata: ByteArray = ByteArray("CALLDATA", b"")
    gasprice: uint256 = BW(0x12)

    returndata: List[z3.BitVecRef] = field(default_factory=list)
    success: Optional[bool] = None

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    path_constraints: List[Constraint] = field(default_factory=list)

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    def copy(self) -> State:
        return State(
            suffix=self.suffix,
            pc=self.pc,
            stack=self.stack.copy(),
            memory=self.memory.copy(),
            address=self.address,
            origin=self.origin,
            caller=self.caller,
            callvalue=self.callvalue,
            calldata=self.calldata,
            gasprice=self.gasprice,
            returndata=self.returndata,
            success=self.success,
            path_constraints=self.path_constraints.copy(),
            path=self.path,
        )

    def constrain(self, solver: z3.Optimize, minimize: bool = False) -> None:
        if minimize:
            solver.minimize(self.callvalue)
            solver.minimize(self.calldata.length())

        # TODO: a contract could, in theory, call itself...
        solver.assert_and_track(self.address != self.origin, f"ADDROR{self.suffix}")
        solver.assert_and_track(self.address != self.caller, f"ADDRCL{self.suffix}")

        for i, constraint in enumerate(self.path_constraints):
            solver.assert_and_track(constraint, f"PC{i}{self.suffix}")

    # def is_changed(self, solver: z3.Optimize, since: State) -> bool:
    #     assert self.success is True

    #     # TODO: constrain further to eliminate no-op writes?
    #     if len(self.storage.written) > 0:
    #         return True

    #     # Check if any address other than the contract itself has increased
    #     for addr in self.balances.written:
    #         if do_check(
    #             solver,
    #             z3.And(
    #                 addr != self.address,
    #                 cast(z3.BitVecRef, self.balances.array[addr])
    #                 > cast(z3.BitVecRef, since.balances.array[addr]),
    #             ),
    #         ):
    #             return True

    #     return False
