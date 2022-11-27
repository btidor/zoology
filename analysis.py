#!/usr/bin/env python3

from typing import Dict, Iterator, List

import z3

from common import Instruction, Predicate, State, do_check, goal
from disassembler import disassemble
from universal import print_solution, universal_transaction


def analyze(instructions: List[Instruction], jumps: Dict[int, int]) -> None:
    goals: Dict[str, List[Predicate]] = {}
    for solver, start, end in universal_transaction(instructions, jumps):
        description = describe_state(solver, end)

        if not do_check(solver, *goal(start, end)):
            continue

        candidates = []
        for candidate in candidate_safety_predicates(end):
            if not do_check(solver, *goal(start, end), candidate.eval(start)):
                # (1) In order to be a valid safety predicate, it must preclude
                # this transaction when applied to the start state
                candidates.append(candidate)
        goals[description] = candidates

    for solver, start, end in universal_transaction(instructions, jumps):
        if not end.is_changed(solver, start):
            continue  # ignore no-ops

        for description, candidates in goals.items():
            # (2) In order to be a valid safety predicate, there must be no STEP
            # transition from P -> ~P
            filtered = []
            for candidate in candidates:
                # TODO: some of these solutions are incorrect!
                constraints = [
                    candidate.eval(start),
                    z3.Not(candidate.eval(end)),
                ]
                check = do_check(solver, *constraints)
                print(description, candidate, check)
                if check == False:
                    filtered.append(candidate)
                else:
                    print_solution(
                        solver,
                        start,
                        end,
                        *constraints,
                        debug_key=candidate.storage_key,
                    )
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
    for i, key in enumerate(state.storage.accessed):
        yield Predicate(
            lambda state: z3.And(
                z3.UGE(state.contribution, state.extraction),
                z3.UGE(state.contribution - state.extraction, state.storage.array[key]),
            ),
            f"balance{i}",
            key,
        )


def describe_state(solver: z3.Solver, state: State) -> str:
    state.constrain(solver)
    solver.minimize(state.callvalue)
    solver.minimize(state.calldata.length())
    assert do_check(solver)
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
