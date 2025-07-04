#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
import sys
import time
from dataclasses import dataclass
from heapq import heappop, heappush
from typing import Any, Self

from bytes import Bytes
from disassembler import abiencode
from environment import Contract, Transaction
from loops import flatten_loops
from sequence import Sequence
from smt import (
    Constraint,
    Uint64,
    Uint160,
    Uint256,
    describe,
)
from snapshot import LEVEL_FACTORIES, PLAYER, PROXY, snapshot_contracts
from solution import Solution, Validator
from state import Descend, Jump, State, Termination, Unreachable
from vm import execute, step

TSTART = int(time.time())

count = 0


def search(
    beginning: Sequence, validator: Validator, depth: int, verbose: int = 0
) -> Solution | None:
    """Symbolically execute the given level until a solution is found."""
    queue = list[Node]()
    for head in make_heads(beginning):
        heappush(queue, Node(beginning, head))
    while queue:
        node = heappop(queue)
        prefix, state = node.prefix, node.state
        while isinstance(state.pc, int):
            if verbose > 2:
                print(state.program.instructions[state.pc])
            match step(state):
                case None:
                    if verbose > 2:
                        for x in reversed(state.stack):
                            print(" ", describe(x))
                    continue
                case Jump(targets):
                    for target in targets:
                        heappush(queue, Node(prefix, target))
                    break
                case Descend(substates):
                    for substate in substates:
                        heappush(queue, Node(prefix, substate))
                    break
                case Unreachable():
                    break

        if not isinstance(state.pc, Termination):
            continue
        if state.recursion is not None:
            # We need to collect *all* terminal states, since if the
            # subcontract reverts the parent contract will continue to
            # execute.
            heappush(queue, Node(prefix, state.recursion(state)))
            continue
        if not state.pc.success:
            continue
        state.cleanup()
        candidate = prefix.extend(state)
        match result := check_candidate(candidate, validator, verbose):
            case True:
                if len(candidate.states) > depth:
                    continue
                for head in make_heads(candidate):
                    heappush(queue, Node(candidate, head))
            case False:
                continue
            case Solution():
                return result
    return None


@dataclass(frozen=True, slots=True)
class Node:
    """A state on the search heap, with its history."""

    prefix: Sequence
    state: State

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def __lt__(self, other: Any) -> bool:
        if not isinstance(other, Node):
            return NotImplemented
        return self.state < other.state


def starting_sequence(
    contracts: dict[int, Contract], factory: Uint160, /, *, prints: bool = False
) -> Sequence:
    """Call createInstance to set up the level."""
    # ASSUMPTION: the only contracts in existence are the ones related to the
    # level factory. This means precompiled contracts are not available!
    assert (arg0 := PLAYER.reveal()) is not None
    calldata = abiencode("createInstance(address)") + arg0.to_bytes(32)
    start = State(
        transaction=Transaction(
            origin=PLAYER,
            caller=PLAYER,
            address=factory,
            calldata=Bytes(calldata),
            callvalue=Uint256(10**15),
        ),
        contracts=contracts,
        mystery_proxy=PROXY,
        mystery_size=Uint256("MYSTERYSIZE"),
    )

    # ASSUMPTION: the only accounts with a nonzero balance belong to the player
    # and the factory contract.
    start.balances[PLAYER] = Uint256(10**18)
    start.balances[start.transaction.address] = start.transaction.callvalue

    generator = execute(start, prints=prints)
    try:
        while True:
            line = next(generator)
            vprint(line + "\n")
    except StopIteration as e:
        end = e.value
        assert isinstance(end, State)

    assert isinstance(end.pc, Termination)
    assert (data := end.pc.returndata.reveal()) is not None
    error = data[68:].strip().decode()
    assert end.pc.success, f"createInstance() failed{': ' + error if error else ''}"
    instance = Uint160(int.from_bytes(data))

    for contract in end.contracts.values():
        if contract.invisible:
            continue
        contract.program = flatten_loops(contract.program)

    return Sequence(
        factory,
        instance,
        PLAYER,
        PROXY,
        end,
    )


def make_heads(prefix: Sequence) -> list[State]:
    """Simulate a symbolic transaction on top of the given prefix."""
    heads = list[State]()
    suffix = f"@{len(prefix.states)}"
    previous, block = prefix.states[-1], prefix.blocks[len(prefix.states) - 1]
    for address in reversed(list(previous.contracts.keys())):
        if previous.contracts[address].invisible:
            continue  # skip factory contracts
        head = State(
            suffix=suffix,
            # ASSUMPTION: each call to the level takes place in a different
            # block, and the blocks are consecutive.
            block=block,
            transaction=Transaction(
                address=Uint160(address),
                origin=PLAYER,
                # ASSUMPTION: all transactions are originated by the player, but
                # may (or may not!) be bounced through a "proxy" contract.
                caller=Constraint(f"CALLERAB{suffix}").ite(PLAYER, PROXY),
                # ASSUMPTION: each transaction sends less than ~18 ETH.
                callvalue=Uint64(f"CALLVALUE{suffix}").into(Uint256),
                calldata=Bytes.symbolic(f"CALLDATA{suffix}"),
                gasprice=Uint256(f"GASPRICE{suffix}"),
            ),
            sha3=copy.deepcopy(previous.sha3),
            contracts=copy.deepcopy(previous.contracts),
            balances=copy.deepcopy(previous.balances),
            solver=copy.deepcopy(previous.solver),
            mystery_proxy=PROXY,
            mystery_size=previous.mystery_size,
            gas_count=0,
            # Search strategy: each transaction pushes the sequence into the
            # subsequent search stage. We apply a greater penalty than with
            # CALL, etc. since transactions have greater fanout (they create
            # more subsequent states).
            cost=previous.cost + 16 if len(prefix.states) > 1 else 0,
        )
        # Because the callvalue of each head is about 16 times less than the
        # player's starting balance, we can guarantee that the transfer always
        # succeeds. This allows us to avoid adding a costly underflow check to
        # the constraint.
        head.balances[head.transaction.origin] -= head.transaction.callvalue
        head.balances[head.transaction.address] += head.transaction.callvalue
        heads.append(head)

    return heads


def check_candidate(
    candidate: Sequence, validator: Validator, verbose: int
) -> bool | Solution:
    """Check whether a sequence solves the level."""
    global count
    if verbose:
        vprint(f"- {candidate.pz()} ({candidate.states[-1].cost})\n")
        vprint(f"  {':'.join(candidate.states[-1].trace)}\n")
    else:
        if count > 0:
            if count % 32 == 0:
                vprint("\n")
            if count % (32 * 16) == 0:
                vprint("\n")
        vprint(f"{len(candidate.states) - 1:X}")
    count += 1

    # We consider a state "changed" if a write to storage has occurred *or* if
    # it's a pure transfer of value. The latter are represented by a
    # SELFDESTRUCT -- it's more general than a `receve()` method because it
    # always succeeds.
    if not candidate.states[-1].changed:
        vprint("  > read-only\n" if verbose else ".")
        return False

    if not candidate.solver.check():
        vprint("  ! constraining error\n" if verbose else "!")
        return False

    if verbose:
        solver = copy.deepcopy(candidate.solver)
        candidate.narrow(solver)
        newline = True
        for part in candidate.describe(solver):
            if newline:
                vprint("  : ")
                newline = False
            vprint(part)
            if part.endswith("\n"):
                newline = True

    if solution := validator.check(candidate):
        vprint("  > found solution!\n" if verbose else "#")
        return solution
    else:
        vprint("  > candidate\n" if verbose else "*")
        return True


def vprint(part: str) -> None:
    """Print a partial line of debugging output."""
    if "args" in globals():
        print(part, end="")
        sys.stdout.flush()


def handle_level(factory: Uint160, args: argparse.Namespace) -> None:
    """Solve an Ethernaut level (from the cli)."""
    contracts = snapshot_contracts(factory)
    vprint("C")
    beginning = starting_sequence(contracts, factory, prints=(args.verbose > 2))
    vprint("V")
    validator = Validator(beginning, prints=(args.verbose > 2))
    vprint("a" if validator.constraint is None else "A")

    if solution := validator.check(beginning):
        pass  # simple SELFDESTRUCT, or a bug
    else:
        vprint("*\n")

    if args.verbose > 1:
        for address, contract in beginning.states[-1].contracts.items():
            vprint("- 0x" + address.to_bytes(20).hex())
            vprint(" (*)\n" if address == beginning.instance.reveal() else "\n")
            assert (code := contract.program.code.reveal()) is not None
            vprint(": " + code.hex() + "\n")

    if solution is None:
        solution = search(beginning, validator, args.depth, verbose=args.verbose)
        if not solution:
            vprint("\tno solution\n")
            return

    newline = True
    indent = 0
    vprint(f"\nResult    | {int(time.time()) - TSTART:06}\n")
    indent = 2
    for part in solution.describe():
        if newline:
            vprint(" " * indent)
            newline = False
        vprint(part)
        if part.endswith("\n"):
            newline = True


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-l", "--level", help="select which level(s) to run", action="append", type=int
    )
    parser.add_argument(
        "-d", "--depth", help="maximum number of transactions", type=int, default=10
    )
    parser.add_argument("-v", "--verbose", action="count", default=0)
    args = parser.parse_args()
    if args.level is None:
        args.level = list(range(len(LEVEL_FACTORIES)))
    for i in args.level:
        if i < 0 or i >= len(LEVEL_FACTORIES):
            raise ValueError(f"invalid level: {i}")

    for i in args.level:
        factory = LEVEL_FACTORIES[i]
        vprint(f"Level {i:03} | L")
        handle_level(factory, args)
