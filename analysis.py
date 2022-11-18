#!/usr/bin/env python3

from typing import Dict, List

import z3
from Crypto.Hash import keccak

from common import (
    BW,
    Block,
    ByteArray,
    Instruction,
    IntrospectableArray,
    State,
    solver_stack,
)
from disassembler import disassemble
from vm import execute


def analyze(
    instructions: List[Instruction],
    jumps: Dict[int, int],
) -> None:
    start = State(
        jumps=jumps,
        address=z3.BitVec("ADDRESS", 160),
        origin=z3.BitVec("ORIGIN", 160),
        caller=z3.BitVec("CALLER", 160),
        callvalue=z3.BitVec("CALLVALUE", 256),
        calldata=ByteArray("CALLDATA"),
        gasprice=z3.BitVec("GASPRICE", 256),
        storage=IntrospectableArray("STORAGE", z3.BitVecSort(256), z3.BitVecSort(256)),
        balances=IntrospectableArray(
            "BALANCES", z3.BitVecSort(160), z3.BitVecSort(256)
        ),
    )
    block = Block()
    solver = z3.Optimize()

    states = [start]
    while len(states) > 0:
        s = states.pop()

        with solver_stack(solver):
            s.constrain(solver)
            check = solver.check()

            if check == z3.sat:  # OK
                if s.success is False:
                    # Ignore executions that REVERT, since they have no effect
                    # on permanent storage.
                    pass
                elif s.success is True:
                    # Success! This execution RETURNs. Now check whether any
                    # goal was met.
                    if check_solution(start, s, solver):
                        handle_solution(start, s, solver)
                    else:
                        pass
                else:
                    # Ordinary fork in execution, keep going...
                    states += execute(instructions, block, s)
            elif check == z3.unsat:
                # We took an illegal turn at the last JUMPI. This branch is
                # unreachable, ignore it.
                pass
            else:
                raise Exception("z3 evaluation timed out")


def check_solution(start: State, end: State, solver: z3.Solver) -> bool:
    solver.assert_and_track(
        z3.Or(
            start.balances[end.origin] > end.balances[end.origin],
            start.balances[end.caller] > end.balances[end.caller],
        ),
        "GOAL:BALANCE",
    )
    check = solver.check()
    if check == z3.sat:
        return True
    elif check == z3.unsat:
        return False
    else:
        raise Exception("z3 evaluation timed out")


def handle_solution(start: State, end: State, solver: z3.Solver) -> None:
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
    print(f"{hex(end.path)}\t{'RETURN' if end.success else 'REVERT'}\t{rdata}")

    for skey in end.sha3keys:
        key = m.eval(skey, True)
        data = key.as_long().to_bytes(key.size() // 8, "big")
        hash = keccak.new(data=data, digest_bits=256)
        digest = int.from_bytes(hash.digest(), "big")
        solver.assert_and_track(skey == key, "SHAKEY")
        solver.assert_and_track(end.sha3hash[skey.size()][skey] == BW(digest), "SHAVAL")
        assert solver.check() == z3.sat
        m = solver.model()

    value = m.eval(end.callvalue).as_long()
    if value:
        print(f"Value\tETH {(value):011,}")

    print(f"Data\t({m.eval(end.calldata.length())}) 0x", end="")
    for i in range(m.eval(end.calldata.length()).as_long()):
        b = m.eval(end.calldata.get(i))
        if z3.is_bv_value(b):
            print(b.as_long().to_bytes(1, "big").hex(), end="")
        else:
            print("??", end="")
        if i == 3:
            print(" ", end="")
    print()
    if z3.is_bv_value(m.eval(end.address)):
        print(f"Address\t0x{m.eval(end.address).as_long().to_bytes(20, 'big').hex()}")
    if z3.is_bv_value(m.eval(end.origin)):
        print(f"Origin\t0x{m.eval(end.origin).as_long().to_bytes(20, 'big').hex()}")
    if z3.is_bv_value(m.eval(end.caller)):
        print(f"Caller\t0x{m.eval(end.caller).as_long().to_bytes(20, 'big').hex()}")
    if z3.is_bv_value(m.eval(end.gasprice)):
        print(f"Gas\tETH {m.eval(end.gasprice).as_long():09,}")

    print_array("Balance", m, start.balances, end.balances)
    print_array("Storage", m, start.storage, end.storage)
    print()


def print_array(
    name: str, m: z3.Model, start: IntrospectableArray, end: IntrospectableArray
) -> None:
    concrete = {}
    for sym in end.accessed:
        key = m.eval(sym)
        concrete[
            f"0x{key.as_long():x}" if z3.is_bv_value(key) else str(key)
        ] = f"0x{m.eval(start.array[sym], True).as_long():x}"

    if len(concrete) > 0:
        print(name, end="")
        for key in sorted(concrete.keys()):
            print(f"\t{key} ", end="")
            if len(key) > 16:
                print("\n\t", end="")
            print(f"-> {concrete[key]}")


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    analyze(instructions, jumps)
    print("Analysis Complete")
