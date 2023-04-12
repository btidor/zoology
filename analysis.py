#!/usr/bin/env python3
"""Performs multi-transaction analysis to find safety violations."""

from typing import Callable, Iterator

from Crypto.Hash import keccak

from disassembler import Program, disassemble
from sha3 import SHA3
from smt import Constraint, Uint160, Uint256
from solver import Solver
from state import State, Termination
from universal import constrain_to_goal, universal_transaction


def analyze(program: Program) -> None:
    print("Ownership: Universal Analysis")
    sha3 = SHA3()
    ownership: list[Predicate] = []
    for start, end in universal_transaction(program, sha3, ""):
        solver = Solver()
        end.constrain(solver)

        description = describe_state(solver, end)

        constrain_to_goal(solver, start, end)
        if not solver.check():
            continue

        print(f" - {description}")
        for candidate in ownership_safety_predicates(end):
            if not solver.check(candidate.eval(start)):
                # (1) In order to be a valid safety predicate, it must preclude
                # this transaction when applied to the start state
                print(f"   {candidate}")
                ownership.append(candidate)

    print()
    print("Ownership: Elimination")
    for start, end in universal_transaction(program, sha3, "^"):
        if not end.is_changed(start):
            continue  # ignore no-ops

        # (2) In order to be a valid safety predicate, there must be no STEP
        # transition from P -> ~P
        for candidate in ownership:
            solver = Solver()
            end.constrain(solver)
            candidate.state.constrain(solver)
            solver.assert_and_track(candidate.eval(start))
            solver.assert_and_track(~candidate.eval(end))
            if solver.check():
                # STEP transition found: constraint is eliminated
                print(f" - {candidate}")
                print(f"   {describe_state(solver, end)}")

    print()
    print("Balance: Universal Analysis")
    additional: list[str] = []
    balance: list[Predicate] = []
    for start, end in universal_transaction(program, sha3, "^"):
        solver = Solver()
        end.constrain(solver)

        description = describe_state(solver, end)

        constrain_to_goal(solver, start, end)
        for predicate in ownership:
            solver.assert_and_track(predicate.eval(start))
        if not solver.check():
            continue

        print(f" - {description}")
        additional.append(description)
        for candidate in balance_safety_predicates(end):
            if not solver.check(candidate.eval(start)):
                # (1) In order to be a valid safety predicate, it must preclude
                # this transaction when applied to the start state
                print(f"   {candidate}")
                balance.append(candidate)

    print()
    print("Balance: Elimination")
    for start, end in universal_transaction(program, sha3, "^"):
        if not end.is_changed(start):
            continue  # ignore no-ops

        # (2) In order to be a valid safety predicate, there must be no STEP
        # transition from P -> ~P
        for candidate in balance:
            solver = Solver()
            end.constrain(solver)
            for predicate in ownership:
                solver.assert_and_track(predicate.eval(start))
            candidate.state.constrain(solver)
            solver.assert_and_track(candidate.eval(start))
            solver.assert_and_track(~candidate.eval(end))
            if solver.check():
                # STEP transition found: constraint is eliminated
                print(f" - {candidate}")
                print(f"   {describe_state(solver, end)}")


class Predicate:
    def __init__(
        self,
        expression: Callable[[State], Constraint],
        description: str,
        state: State,
        storage_key: Uint256 | None = None,
    ) -> None:
        self.expression = expression
        self.description = description
        self.state = state
        self.storage_key = storage_key

    def eval(self, state: State) -> Constraint:
        return self.expression(state)

    def __repr__(self) -> str:
        return self.description


def ownership_safety_predicates(state: State) -> Iterator[Predicate]:
    for key in state.contract.storage.accessed:
        if key.maybe_unwrap() is None:
            continue
        yield Predicate(
            lambda state: Constraint.all(
                state.transaction.origin
                != state.contract.storage.peek(key).into(Uint160),
                state.transaction.caller
                != state.contract.storage.peek(key).into(Uint160),
            ),
            f"$OWNER[{key.describe()}]",
            state,
        )


def balance_safety_predicates(state: State) -> Iterator[Predicate]:
    used: set[str] = set()
    for key in state.contract.storage.accessed:
        if u := key.maybe_unwrap():
            index = hex(u)[2:]
        else:
            hash = keccak.new(data=str(key).encode(), digest_bits=256).hexdigest()
            if hash in used:
                continue
            used.add(hash)
            index = hash[:8] + "?"
        yield Predicate(
            lambda state: Constraint.all(
                state.universe.contribution >= state.universe.extraction,
                state.universe.contribution - state.universe.extraction
                >= state.contract.storage.peek(key),
            ),
            f"$BALANCE[{index}]",
            state,
            key,
        )


def describe_state(solver: Solver, state: State) -> str:
    assert solver.check()
    assert isinstance(state.pc, Termination)
    assert state.pc.success is True

    return "0x" + state.transaction.calldata.describe(solver)


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)
    analyze(program)
