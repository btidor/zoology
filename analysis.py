#!/usr/bin/env python3

from typing import Dict, List, Optional, Tuple, TypeAlias, cast

import z3

from common import (
    BA,
    Block,
    ByteArray,
    Instruction,
    IntrospectableArray,
    State,
    do_check,
    solver_stack,
)
from disassembler import disassemble
from transaction import simulate_transaction

Transition: TypeAlias = Tuple[int, Optional[State], Optional[State]]
History: TypeAlias = List[Transition]


def analyze(instructions: List[Instruction], jumps: Dict[int, int]) -> None:
    # TODO: transactions may span multiple blocks
    block = Block()
    solver = z3.Optimize()

    # TODO: support transaction chains from multiple addresses
    origin = z3.BitVec("ORIGIN", 160)
    address: z3.BitVec = z3.BitVec("ADDRESS", 160)
    start = State(
        jumps=jumps,
        address=address,
        # TODO: properly constrain ORIGIN to be an EOA and CALLER to either be
        # equal to ORIGIN or else be a non-EOA.
        origin=origin,
        caller=origin,
        callvalue=z3.BitVec("CALLVALUE#0", 256),
        calldata=ByteArray("CALLDATA#0"),
        gasprice=z3.BitVec("GASPRICE#0", 256),
        # TODO: the balances of other accounts can change between transactions
        # (and the balance of this contract account too, via SELFDESTRUCT). How
        # do we model this?
        balances=IntrospectableArray(
            "BALANCES", z3.BitVecSort(160), z3.BitVecSort(256)
        ),
        storage=IntrospectableArray("STORAGE", z3.BitVecSort(256), z3.BitVecSort(256)),
    )

    histories: List[History] = [[(-1, None, None)]]
    while len(histories) > 0:
        history = histories.pop()
        ptx, _, previous = history[-1]
        if previous is None:
            start = State(
                jumps=jumps,
                address=address,
                # TODO: properly constrain ORIGIN to be an EOA and CALLER to
                # either be equal to ORIGIN or else be a non-EOA.
                origin=origin,
                caller=origin,
                # TODO: the balances of other accounts can change between
                # transactions (and the balance of this contract account too,
                # via SELFDESTRUCT). How do we model this?
                balances=IntrospectableArray(
                    "BALANCES", z3.BitVecSort(160), z3.BitVecSort(256)
                ),
                storage=IntrospectableArray(
                    "STORAGE", z3.BitVecSort(256), z3.BitVecSort(256)
                ),
            )
        else:
            start = previous.copy()

        start.callvalue = z3.BitVec(f"CALLVALUE#{ptx+1}", 256)
        start.calldata = ByteArray(f"CALLDATA#{ptx+1}")
        start.gasprice = z3.BitVec(f"GASPRICE#{ptx+1}", 256)

        for end in simulate_transaction(solver, block, instructions, start):
            history.append((ptx + 1, start, end))
            if check_goal(solver, start, end):
                cond = is_conditional(solver, end)
                if cond is None:
                    print("TRM\t", end="")
                    print_history(solver, history)
                    return
                print("CND\t", end="")
                print_history(solver, history)
                cast(State, history[-1][2]).constraints.append(cond)
            elif end.is_changed():
                histories.append(history)
            else:
                pass


def check_goal(solver: z3.Solver, start: State, end: State) -> bool:
    with solver_stack(solver):
        solver.assert_and_track(
            end.balances[end.origin] > start.balances[end.origin], "GOAL:BALANCE"
        )
        return do_check(solver)


def is_conditional(solver: z3.Solver, state: State) -> Optional[z3.ExprRef]:
    # First, check the owner hypothesis: that an address in a storage slot
    # matches the caller or origin.
    #
    # TODO: handle cases where the owner is packed with other variables in the
    # slot (taint tracking? brute force?)
    state.constrain(solver)
    solver.minimize(state.callvalue)
    solver.minimize(state.calldata.length())
    assert solver.check() == z3.sat
    m = solver.model()

    origin = m.eval(state.origin, True).as_long()
    caller = m.eval(state.caller, True).as_long()
    for key in state.storage.accessed:
        val = m.eval(state.storage.array[key], True).as_long()
        if val != origin and val != caller:
            continue
        cond = z3.And(
            state.origin != z3.Extract(159, 0, state.storage.array[key]),
            state.caller != z3.Extract(159, 0, state.storage.array[key]),
        )
        if do_check(solver, [cond]) == False:
            return cond

    # TODO: the owner hypothesis eliminates the first degenerate case (Px1255),
    # a call to collectAllocations() by the owner. We now need to eliminate the
    # second degenerate case (Px1155), a call to sendAllocation(address) using
    # an address that has preexisting balance.
    return z3.BoolRef(False)


def print_history(solver: z3.Solver, history: History) -> None:
    tx = history[-1][0]
    end = cast(State, history[-1][2])
    end.constrain(solver)
    solver.minimize(end.callvalue)
    solver.minimize(end.calldata.length())
    assert solver.check() == z3.sat
    m = solver.model()

    if len(end.returndata) > 0:
        rdata = "0x" + "".join(
            m.eval(b, True).as_long().to_bytes(1, "big").hex() for b in end.returndata
        )
    else:
        rdata = "-"
    print(
        f"TX{tx:02}\t{hex(end.path)}\t{'RETURN' if end.success else 'REVERT'}\t{rdata}"
    )


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    analyze(instructions, jumps)
    print("Analysis Complete")
