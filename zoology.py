#!/usr/bin/env python3
"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import argparse
import copy
import sys
import time
from functools import reduce
from itertools import chain

from bytes import Bytes
from disassembler import abiencode
from environment import ConcreteContract, Contract, Transaction
from sequence import Sequence, Solution, Validator
from sha3 import SHA3
from smt import (
    Array,
    ConstrainingError,
    Constraint,
    Solver,
    Uint64,
    Uint160,
    Uint256,
)
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import State, Termination
from universal import universal_transaction
from vm import printable_execution

PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)

TSTART = int(time.time())


def create_transaction(factory: Uint160) -> Transaction:
    """Return a Transaction representing a call to createInstance."""
    assert (arg0 := PLAYER.reveal()) is not None
    calldata = abiencode("createInstance(address)") + arg0.to_bytes(32)
    return Transaction(
        origin=PLAYER,
        caller=PLAYER,
        address=factory,
        calldata=Bytes(calldata),
        callvalue=Uint256(10**15),
    )


def validate_transaction(factory: Uint160, instance: Uint160) -> Transaction:
    """Return a Transaction representing a call to validateInstance."""
    assert (arg0 := instance.reveal()) is not None
    assert (arg1 := PLAYER.reveal()) is not None
    calldata = (
        abiencode("validateInstance(address,address)")
        + arg0.to_bytes(32)
        + arg1.to_bytes(32)
    )
    return Transaction(
        origin=PLAYER,
        caller=PLAYER,
        address=factory,
        calldata=Bytes(calldata),
    )


def starting_sequence(
    contracts: dict[int, Contract], factory: Uint160, prints: bool = False
) -> Sequence:
    """Call createInstance to set up the level."""
    # ASSUMPTION: the only contracts in existence are the ones related to the
    # level factory. This means precompiled contracts are not available!
    start = State(
        transaction=create_transaction(factory),
        contracts=contracts,
        mystery_proxy=PROXY,
        mystery_size=Uint256("MYSTERYSIZE"),
    )

    # ASSUMPTION: the only account with a nonzero balance belongs to the player.
    start.balances[PLAYER] = Uint256(10**18)
    start.transfer(
        start.transaction.caller, start.transaction.address, start.transaction.callvalue
    )

    generator = printable_execution(start)
    try:
        while True:
            line = next(generator)
            if prints:
                vprint(line + "\n")
    except StopIteration as e:
        end = e.value
        assert isinstance(end, State)

    assert isinstance(end.pc, Termination)
    assert (data := end.pc.returndata.reveal()) is not None
    error = data[68:].strip().decode()
    assert end.pc.success, f"createInstance() failed{': ' + error if error else ''}"
    instance = Uint160(int.from_bytes(data))
    return Sequence(
        factory,
        instance,
        PLAYER,
        PROXY,
        end,
        validate_transaction(factory, instance),
    )


def validate_universal(sequence: Sequence, prints: bool = False) -> Validator | None:
    """Symbolically interpret validateInstance as a function, if possible."""
    carryover, block = sequence.subsequent(validation=True)
    start = State(
        suffix="-V",
        block=block,
        transaction=sequence.validate_transaction,
        sha3=SHA3(),  # validator optimization requires this SHA3 go unused
        contracts={},
        balances=Array[Uint160, Uint256]("BALANCE"),
        constraint=carryover.constraint,
        mystery_proxy=PROXY,
        mystery_size=carryover.mystery_size,
        gas_count=0,
        # ASSUMPTION: when executing validateInstance(...), we only call into
        # contracts defined at the outset, and no contract calls itself.
        skip_self_calls=True,
    )

    for reference in carryover.contracts.values():
        assert (a := reference.address.reveal()) is not None
        assert isinstance(reference, ConcreteContract)
        start = start.with_contract(
            ConcreteContract(
                address=reference.address,
                program=reference.program,
                storage=Array[Uint256, Uint256](f"STORAGE@{a.to_bytes(20).hex()}"),
                nonce=reference.nonce,
            ),
            True,
        )

    predicates = list[Constraint]()
    for end in universal_transaction(start, check=False, prints=prints):
        assert isinstance(end.pc, Termination)

        # This logic needs to match State.constrain(). We don't need to worry
        # about narrowing because SHA3 is not invoked (see check below).
        b: Uint256 = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector()
        predicates.append(end.constraint & (b != Uint256(0)))

        if len(end.contracts) > len(carryover.contracts):
            # We can't handle validators that create contracts. That would be
            # pretty strange, though.
            raise NotImplementedError

        if end.sha3.free or end.sha3.symbolic:
            # We can't currently handle feeding the global SHA3 instance into
            # the validator. Fall back to running validateInstance with concrete
            # inputs at every step.
            return None

    assert predicates
    try:
        # Eligible for validator optimization!
        return Validator(reduce(lambda p, q: p | q, predicates, Constraint(False)))
    except ValueError:
        # Validator expression uses an unsupported variable; fall back.
        return None


def validate_concrete(sequence: Sequence, validator: Validator | None) -> Solution:
    """Simulate the execution of validateInstance on the given sequence."""
    if validator is not None:
        return Solution(sequence, validator.translate(sequence))

    carryover, block = sequence.subsequent(validation=True)
    start = State(
        suffix="-V",
        block=block,
        transaction=sequence.validate_transaction,
        sha3=carryover.sha3,
        contracts=carryover.contracts,
        balances=carryover.balances,
        constraint=carryover.constraint,
        mystery_proxy=PROXY,
        mystery_size=carryover.mystery_size,
        gas_count=0,
    )

    for end in universal_transaction(start):
        assert isinstance(end.pc, Termination)
        solver = Solver()
        candidate = sequence.extend(end)
        candidate.constrain(solver, check=False)
        ok = end.pc.returndata.slice(Uint256(0), Uint256(32)).bigvector() != Uint256(0)
        solver.add(ok)
        if solver.check():
            end.sha3.narrow(solver)
            return Solution(sequence, end)
    return Solution(sequence, None)


def search(
    beginning: Sequence, validator: Validator | None, depth: int, verbose: int = 0
) -> tuple[Solution, Solver] | None:
    """Symbolically execute the given level until a solution is found."""
    sequences = [beginning]
    z = ""
    for i in range(depth):
        suffix = f"@{i+1}"
        if z != "\n":
            vprint("\n")
        vprint(f"Trans {i+1:03} | {int(time.time())-TSTART:06}\n")
        j = 0
        subsequent = list[Sequence]()
        for sequence in sequences:
            for address in reversed(list(sequence.peek_contracts())):
                carryover, block = sequence.subsequent()
                if carryover.contracts[address].invisible:
                    continue  # skip factory contracts
                start = State(
                    suffix=suffix,
                    # ASSUMPTION: each call to the level takes place in a
                    # different block, and the blocks are consecutive.
                    block=block,
                    transaction=Transaction(
                        address=Uint160(address),
                        origin=PLAYER,
                        # ASSUMPTION: all transactions are originated by the
                        # player, but may (or may not!) be bounced through a
                        # "proxy" contract.
                        caller=Constraint(f"CALLERAB{suffix}").ite(PLAYER, PROXY),
                        # ASSUMPTION: each transaction sends less than ~18 ETH.
                        callvalue=Uint64(f"CALLVALUE{suffix}").into(Uint256),
                        calldata=Bytes.symbolic(f"CALLDATA{suffix}"),
                        gasprice=Uint256(f"GASPRICE{suffix}"),
                    ),
                    sha3=carryover.sha3,
                    contracts=carryover.contracts,
                    balances=carryover.balances,
                    constraint=carryover.constraint,
                    mystery_proxy=PROXY,
                    mystery_size=carryover.mystery_size,
                    gas_count=0,
                )
                start.transfer(
                    start.transaction.origin,
                    start.transaction.address,
                    start.transaction.callvalue,
                    initial=True,
                )

                selfdestruct = copy.deepcopy(start)
                universal = universal_transaction(
                    start, check=False, prints=(verbose > 1)
                )
                for end in chain(universal, (selfdestruct,)):
                    candidate = sequence.extend(end)
                    if verbose:
                        vprint(f"- {candidate.pz()}\n")
                    else:
                        vprint(f"{j:03x}")
                    j += 1
                    z = " " if j % 16 else "\n"

                    # We consider a state "changed" if a write to storage has
                    # occurred *or* if it's a pure transfer of value. The latter
                    # are represented by a SELFDESTRUCT -- it's more general
                    # than a `receve()` method because it always succeeds.
                    if not end.changed and not isinstance(end.pc, int):
                        if verbose:
                            vprint("  > read-only\n")
                        else:
                            vprint("." + z)
                        continue

                    if verbose:
                        try:
                            solver = Solver()
                            candidate.constrain(solver)
                            candidate.narrow(solver)
                            newline = True
                            for part in candidate.describe(solver):
                                if newline:
                                    vprint("  : ")
                                    newline = False
                                vprint(part)
                                if part.endswith("\n"):
                                    newline = True
                        except ConstrainingError:
                            vprint("  ! constraining error\n")
                            continue

                    solution = validate_concrete(candidate, validator)
                    solver = Solver()
                    solution.constrain(solver, check=False)
                    if solver.check():
                        solution.narrow(solver)
                        if verbose:
                            vprint("  > found solution!\n")
                        else:
                            vprint("#" + z)
                        return solution, solver

                    if not verbose:
                        try:
                            solver = Solver()
                            candidate.constrain(solver)
                        except ConstrainingError:
                            vprint("!" + z)
                            continue

                    if verbose:
                        vprint("  > candidate\n")
                    else:
                        vprint("*" + z)
                    subsequent.append(candidate)

        sequences = subsequent

    return None


def vprint(part: str) -> None:
    """Print a partial line, if verbose mode is enabled."""
    if "args" in globals():
        print(part, end="")
        sys.stdout.flush()


def handle_level(factory: Uint160, args: argparse.Namespace) -> None:
    """Solve an Ethernaut level (from the cli)."""
    contracts = snapshot_contracts(factory)
    vprint("C")
    beginning = starting_sequence(contracts, factory, prints=(args.verbose > 1))
    vprint("V")
    validator = validate_universal(beginning, prints=(args.verbose > 1))
    vprint("a" if validator is None else "A")
    solution = validate_concrete(beginning, validator)
    vprint("Z")
    solver = Solver()
    solution.constrain(solver, check=False)
    assert not solver.check()
    vprint("*")

    result = search(beginning, validator, args.depth, verbose=args.verbose)
    if result is None:
        vprint("\tno solution\n")
        return

    solution, solver = result
    newline = True
    indent = 0
    vprint(f"\nResult    | {int(time.time())-TSTART:06}\n")
    indent = 2
    for part in solution.describe(solver):
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
