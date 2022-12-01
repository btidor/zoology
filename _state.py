from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Literal, Optional, Union, cast

import z3

from _symbolic import (
    BA,
    BW,
    ByteArray,
    IntrospectableArray,
    do_check,
    uint8,
    uint160,
    uint256,
)


def constrain_to_goal(solver: z3.Optimize, start: State, end: State) -> None:
    solver.assert_and_track(z3.ULT(start.extraction, start.contribution), "GOAL.PRE")
    solver.assert_and_track(z3.UGT(end.extraction, end.contribution), "GOAL.POST")


@dataclass
class Block:
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
class State:
    suffix: str = ""
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

    storage: IntrospectableArray = IntrospectableArray(
        "STORAGE", z3.BitVecSort(256), BW(0)
    )

    # Maps the length of the input data to a Z3 Array which maps symbolic inputs
    # to symbolic hash digests.
    sha3hash: Dict[int, z3.ArrayRef] = field(default_factory=dict)
    sha3keys: List[z3.BitVecRef] = field(default_factory=list)

    # Global map of all account balances.
    balances: IntrospectableArray = IntrospectableArray(
        "BALANCES", z3.BitVecSort(160), BW(0)
    )

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    constraints: List[Union[z3.ExprRef, Literal[True], Literal[False]]] = field(
        default_factory=list
    )

    # Additional constraints imposed by the multi-transaction solver.
    extra: List[z3.ExprRef] = field(default_factory=list)

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    # Tracks how much value has been sent to and received from the contract,
    # respectively, from accounts under the control of our agent. To avoid
    # overflow errors, we track these as two separate unsigned (nonnegative)
    # integers. When doing math to them, we assert that operations never
    # overflow, since there isn't enough ETH in existence to overflow a uint256.
    contribution: uint256 = BW(0)
    extraction: uint256 = BW(0)

    def transfer(self, dst: uint160, val: uint256) -> None:
        self._transfer(self.address, dst, val)
        delta = z3.If(z3.Or(dst == self.caller, dst == self.origin), val, BW(0))
        self.extra.append(z3.BVAddNoOverflow(self.extraction, delta, False))
        self.extraction += delta

    def transfer_initial(self) -> None:
        self._transfer(self.caller, self.address, self.callvalue)
        self.extra.append(z3.BVAddNoOverflow(self.contribution, self.callvalue, False))
        self.contribution += self.callvalue

    def _transfer(self, src: uint160, dst: uint160, val: uint256) -> None:
        # We know this must be true because if `self.balances[src]` goes
        # negative from the transfer, the transaction will revert.
        self.extra.append(z3.BVSubNoUnderflow(self.balances[src], val, False))
        self.extra.append(z3.BVAddNoOverflow(self.balances[dst], val, False))
        self.balances[src] -= val
        self.balances[dst] += val

    def copy(self) -> "State":
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
            storage=self.storage.copy(),
            sha3hash=self.sha3hash.copy(),
            sha3keys=self.sha3keys.copy(),
            balances=self.balances.copy(),
            constraints=self.constraints.copy(),
            extra=self.extra.copy(),
            path=self.path,
            contribution=self.contribution,
            extraction=self.extraction,
        )

    def constrain(self, solver: z3.Optimize, minimize: bool = False) -> None:
        if minimize:
            solver.minimize(self.callvalue)
            solver.minimize(self.calldata.length())

        # TODO: a contract could, in theory, call itself...
        solver.assert_and_track(self.address != self.origin, f"ADDROR{self.suffix}")
        solver.assert_and_track(self.address != self.caller, f"ADDRCL{self.suffix}")

        for i, constraint in enumerate(self.constraints):
            solver.assert_and_track(constraint, f"PC{i}{self.suffix}")

        for i, constraint in enumerate(self.extra):
            solver.assert_and_track(constraint, f"EXTRA{i}{self.suffix}")

        for i, k1 in enumerate(self.sha3keys):
            # TODO: this can still leave hash digests implausibly close to one
            # another, e.g. causing two arrays to overlap; and we don't
            # propagate constraints between transactions correctly
            solver.assert_and_track(
                z3.Extract(255, 128, self.sha3hash[k1.size()][k1]) != 0,
                f"SHA3.NLZ({i}){self.suffix}",
            )
            for j, k2 in enumerate(self.sha3keys):
                if k1.size() != k2.size():
                    continue
                solver.assert_and_track(
                    z3.Implies(
                        k1 != k2,
                        self.sha3hash[k1.size()][k1] != self.sha3hash[k2.size()][k2],
                    ),
                    f"SHA3.DISTINCT({i},{j}){self.suffix}",
                )

    def is_changed(self, solver: z3.Optimize, since: "State") -> bool:
        assert self.success is True

        # TODO: constrain further to eliminate no-op writes?
        if len(self.storage.written) > 0:
            return True

        # Check if any address other than the contract itself has increased
        for addr in self.balances.written:
            if do_check(
                solver,
                z3.And(
                    addr != self.address,
                    cast(z3.BitVecRef, self.balances.array[addr])
                    > cast(z3.BitVecRef, since.balances.array[addr]),
                ),
            ):
                return True

        return False
