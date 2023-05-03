#!/usr/bin/env python3
"""A universal transaction solver."""

import copy
from typing import Iterable, Iterator

from disassembler import Program, disassemble
from environment import Block, Contract, Transaction, Universe
from smt.arrays import Array
from smt.bytes import FrozenBytes, MutableBytes
from smt.sha3 import SHA3
from smt.smt import Uint160, Uint256
from smt.solver import Solver
from state import Descend, Jump, State, Termination
from vm import step


def universal_transaction(
    state: State, filter: bool = True, prints: bool = False
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
    while isinstance(state.pc, int):
        if prints:
            print(state.contract.program.instructions[state.pc])
        match step(state):
            case None:
                if prints:
                    for x in reversed(state.stack):
                        print(" ", x.describe())
                continue
            case Jump(targets):
                for _, next in targets:
                    solver = Solver()
                    next.constrain(solver)
                    if not solver.check():
                        continue
                    yield from universal_transaction(next, filter=filter, prints=prints)
                return
            case Descend(substate, callback):
                # We need to collect *all* terminal states, since if the
                # subcontract reverts the parent contract will continue to
                # execute.
                for subend in universal_transaction(
                    substate, filter=False, prints=prints
                ):
                    next = copy.deepcopy(state)
                    next = callback(next, subend)
                    yield from universal_transaction(next, filter=filter, prints=prints)
                return
            case unknown:
                raise ValueError(f"unknown action: {unknown}")

    assert isinstance(state.pc, Termination)
    if state.pc.success or not filter:
        yield state


def symbolic_start(program: Contract | Program, sha3: SHA3, suffix: str) -> State:
    """Return a fully-symbolic start state."""
    if isinstance(program, Contract):
        contract = program
    else:
        contract = Contract(
            address=Uint160("ADDRESS"),
            program=program,
            storage=Array.symbolic(f"STORAGE{suffix}", Uint256, Uint256),
        )
    # TODO: properly constrain ORIGIN to be an EOA and CALLER to either be equal
    # to ORIGIN or else be a non-EOA
    transaction = Transaction.symbolic(suffix)
    # TODO: the balances of other accounts can change between transactions
    # (and the balance of this contract account too, via SELFDESTRUCT). How
    # do we model this?
    universe = Universe.symbolic(suffix)
    universe.agents = [transaction.origin, transaction.caller]
    universe.codesizes[contract.address] = contract.program.code.length
    universe.codesizes[transaction.origin] = Uint256(0)
    return State(
        suffix=suffix,
        block=Block.symbolic(suffix),
        contract=contract,
        transaction=transaction,
        universe=universe,
        sha3=sha3,
        pc=0,
        stack=[],
        memory=MutableBytes.concrete(),
        children=0,
        latest_return=FrozenBytes.concrete(),
        logs=[],
        gas_variables=[],
        call_variables=[],
        path_constraints=[],
        path=1,
    )


def constrain_to_goal(solver: Solver, start: State, end: State) -> None:
    """
    Apply goal constraints to the given solver instance.

    The "goal" here is our definition of a potential security vulnerability: a
    state tranisition that results in our agent extracting net value from the
    contract.
    """
    solver.assert_and_track(start.universe.extraction <= start.universe.contribution)
    solver.assert_and_track(end.universe.extraction > end.universe.contribution)


def printable_transition(start: State, end: State) -> Iterable[str]:
    """Produce a human-readable description of a given state transition."""
    solver = Solver()
    end.constrain(solver)
    assert solver.check()

    constrain_to_goal(solver, start, end)
    if solver.check():
        for line in _printable_transition(solver, start, end, "🚩 GOAL"):
            yield line
        return

    if end.is_changed(start):
        kind = "📒 SAVE"
    else:
        kind = "  VIEW"

    # Reset so we can extract the model
    solver = Solver()
    end.constrain(solver)
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

    a = solver.evaluate(start.universe.contribution).unwrap(bytes).hex()
    b = solver.evaluate(end.universe.contribution).unwrap(bytes).hex()
    if a != b:
        yield f"Contrib\tETH 0x{a}"
        yield f"\t->  0x{b}"
        yield f""

    a = solver.evaluate(start.universe.extraction).unwrap(bytes).hex()
    b = solver.evaluate(end.universe.extraction).unwrap(bytes).hex()
    if a != b:
        yield f"Extract\tETH 0x{a}"
        yield f"\t->  0x{b}"
        yield f""

    for line in end.universe.balances.printable_diff(
        "Balance", solver, start.universe.balances
    ):
        yield line

    for line in end.contract.storage.printable_diff(
        "Storage", solver, start.contract.storage
    ):
        yield line

    for line in end.sha3.printable(solver):
        yield line


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)

    start = symbolic_start(program, SHA3(), "")
    init = copy.deepcopy(start)
    init.universe.transfer(
        init.transaction.caller,
        init.contract.address,
        init.transaction.callvalue,
    )
    for end in universal_transaction(init):
        for line in printable_transition(start, end):
            print(line)

    print("---  End Universal Transaction\t".ljust(80, "-"))
