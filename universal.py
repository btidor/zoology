#!/usr/bin/env python3
"""A universal transaction solver."""

import copy
from heapq import heappop, heappush
from typing import Iterable, Iterator

from bytes import Bytes
from disassembler import Program
from environment import Block, Contract, Transaction
from sha3 import SHA3
from smt import Array, Solver, Uint160, Uint256, describe
from state import Descend, GasHogCall, Jump, State, Termination, Unreachable
from tests.solidity import load_solidity
from vm import step


def universal_transaction(
    state: State, /, check: bool = True, prints: bool = False
) -> Iterator[State]:
    """
    Compute the "universal transaction" over a fully symbolic input.

    Execute the given program with a fully-symbolic start state. Yield every
    possible state pair `(start, end)`, where `start` is a constant and `end` is
    a state that RETURNs.

    If you're going to further constrain the end states using expressions from a
    prior execution of `universal_transaction()`, the two executions should have
    a different suffix.
    """
    queue = [state]
    while queue:
        state = heappop(queue)
        while isinstance(state.pc, int):
            if prints:
                print(state.program.instructions[state.pc])
            match step(state):
                case None:
                    if prints:
                        for x in reversed(state.stack):
                            print(" ", describe(x))
                    continue
                case Jump(targets):
                    for target in targets:
                        heappush(queue, target)
                    break
                case Descend(substates):
                    for substate in substates:
                        heappush(queue, substate)
                    break
                case Unreachable():
                    break
                case unknown:
                    raise ValueError(f"unknown action: {unknown}")

        if isinstance(state.pc, Termination):
            if state.recursion is not None:
                # We need to collect *all* terminal states, since if the
                # subcontract reverts the parent contract will continue to
                # execute.
                heappush(queue, state.recursion(state))
                continue
            if not state.pc.success:
                continue
            if check:
                solver = Solver()
                solver.add(state.constraint)
                if not solver.check():
                    continue
            yield state


def symbolic_start(program: Contract | Program, sha3: SHA3, suffix: str) -> State:
    """Return a fully-symbolic start state."""
    if isinstance(program, Contract):
        contract = program
    else:
        contract = Contract(
            program=program,
            storage=Array[Uint256, Uint256](f"STORAGE{suffix}"),
            nonce=Uint256(f"NONCE{suffix}"),
        )
    transaction = Transaction(
        address=contract.address,
        origin=Uint160(f"ORIGIN{suffix}"),
        caller=Uint160(f"CALLER{suffix}"),
        callvalue=Uint256(f"CALLVALUE{suffix}"),
        calldata=Bytes.symbolic(f"CALLDATA{suffix}"),
        gasprice=Uint256(f"GASPRICE{suffix}"),
    )
    return State(
        suffix=suffix,
        block=Block.symbolic(suffix),
        transaction=transaction,
        balances=Array[Uint160, Uint256](f"BALANCE{suffix}"),
        sha3=sha3,
        mystery_proxy=Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0),
        mystery_size=Uint256("MYSTERYSIZE"),
        gas_count=0,
    ).with_contract(contract)


def printable_transition(start: State, end: State) -> Iterable[str]:
    """Produce a human-readable description of a given state transition."""
    solver = Solver()
    solver.add(end.constraint)
    assert solver.check()

    if end.changed:
        kind = "📒 SAVE"
    else:
        kind = "  VIEW"

    # Reset so we can extract the model
    assert solver.check()

    for line in _printable_transition(solver, start, end, kind):
        yield line


def _printable_transition(
    solver: Solver, start: State, end: State, kind: str
) -> Iterable[str]:
    assert isinstance(end.pc, Termination)
    result = "RETURN" if end.pc.success else "REVERT"

    yield f"---  {kind}\t{result}\t{end.px()}\t".ljust(80, "-")
    yield ""

    end.narrow(solver)

    values = end.transaction.describe(solver)
    for k, v in values.items():
        yield f"{k}\t{v}"
    if len(values) > 0:
        yield ""

    values = end.describe(solver)
    for k, v in values.items():
        yield f"{k}\t{v}"
    if len(values) > 0:
        yield ""

    for line in end.balances.printable_diff("Balance", solver, start.balances):
        yield line

    for line in end.storage.printable_diff("Storage", solver, start.storage):
        yield line

    for line in end.sha3.printable(solver):
        yield line

    for call in end.calls:
        a = solver.evaluate(call.transaction.address)
        k = solver.evaluate(call.ok.ite(Uint256(1), Uint256(0)))
        kind = (
            "CONSUME ALL GAS"
            if isinstance(call, GasHogCall)
            else "RETURN"
            if k
            else "REVERT"
        )
        yield f"Call\t0x{a.to_bytes(20).hex()}\t{kind}"
    if len(end.calls) > 0:
        yield ""


if __name__ == "__main__":
    program = load_solidity("fixtures/01_Fallback.sol")
    start = symbolic_start(program, SHA3(), "")
    start.skip_self_calls = True
    init = copy.deepcopy(start)
    init.balances[init.transaction.address] = init.transaction.callvalue
    for end in universal_transaction(init):
        for line in printable_transition(start, end):
            print(line)

    print("---  End Universal Transaction\t".ljust(80, "-"))
