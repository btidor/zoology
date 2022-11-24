#!/usr/bin/env python3

from typing import Dict, Iterator, List

import z3

from common import Instruction, Predicate, State, do_check, solver_stack
from disassembler import disassemble
from universal import print_solution, universal_transaction


def analyze(instructions: List[Instruction], jumps: Dict[int, int]) -> None:
    solver = z3.Optimize()

    goals: Dict[str, List[Predicate]] = {}
    for start, end in universal_transaction(solver, instructions, jumps):
        if check_goal(solver, start, end):
            candidates = []
            for candidate in candidate_safety_predicates(end):
                with solver_stack(solver):
                    solver.assert_and_track(
                        candidate.apply(start), f"SAFETY:{candidate}"
                    )
                    if not check_goal(solver, start, end):
                        # (1) In order to be a valid safety predicate, it must
                        # *not* hold in the goal transition start state
                        candidates.append(candidate)

            description = describe_state(solver, end)
            goals[description] = candidates

    for start, end in universal_transaction(solver, instructions, jumps):
        if check_goal(solver, start, end) or not end.is_changed(solver, start):
            # We only want to analyze STEP transitions, so ignore GOAL
            # transitions and no-ops
            continue

        for description, candidates in goals.items():
            # (2) In order to be a valid safety predicate, there must be no STEP
            # transition from P -> ~P
            filtered = []
            for candidate in candidates:
                check = do_check(
                    solver, candidate.apply(start), z3.Not(candidate.apply(end))
                )
                # TODO: debug this!
                print(description.split("\t")[0], hex(end.path), candidate, check)
                print_solution(solver, start, end)
                m = solver.model()
                print(
                    z3.simplify(m.eval(end.contribution)),
                    z3.simplify(m.eval(start.callvalue)),
                )
                if check == False:
                    filtered.append(candidate)
            goals[description] = filtered

    for description, candidates in goals.items():
        if len(candidates) > 0:
            # Successfully constrained goal with safety predicate!
            print("    ✨\t", end="")
        else:
            # Goal is unconstrained [TODO: consider safety predicates that
            # require a chain of transactions to apply]
            print("    💥\t", end="")
        print(description)


def check_goal(solver: z3.Solver, start: State, end: State) -> bool:
    with solver_stack(solver):
        solver.assert_and_track(
            z3.And(
                end.balances[end.origin] > start.balances[end.origin],
                end.balances[end.origin] - start.balances[end.origin]
                > start.contribution,
            ),
            "GOAL:BALANCE",
        )
        return do_check(solver)


def candidate_safety_predicates(state: State) -> Iterator[Predicate]:
    # Ownership Predicate
    for key in state.storage.accessed:
        k = z3.simplify(key)
        if z3.is_bv_value(k):
            yield Predicate(
                lambda state: z3.And(
                    state.origin
                    != z3.Extract(159, 0, state.storage.array[k.as_long()]),
                    state.caller
                    != z3.Extract(159, 0, state.storage.array[k.as_long()]),
                ),
                f"ownership[{hex(k.as_long())}]",
            )

    # Balance Predicate
    for key in state.storage.accessed:
        yield Predicate(
            lambda state: state.contribution >= state.storage.array[key], f"balance*"
        )


def describe_state(solver: z3.Solver, state: State) -> str:
    state.constrain(solver)
    solver.minimize(state.callvalue)
    solver.minimize(state.calldata.length())
    assert solver.check() == z3.sat
    m = solver.model()

    calldata = "0x"
    for i in range(m.eval(state.calldata.length()).as_long()):
        b = m.eval(state.calldata.get(i))
        calldata += f"{b.as_long():02x}" if z3.is_bv_value(b) else "??"
        if i == 3:
            calldata += " "

    assert state.success == True
    return f"Px{state.path:x}\t{calldata}"


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    analyze(instructions, jumps)
