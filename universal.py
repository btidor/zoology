#!/usr/bin/env python3

from typing import Any, Callable, Dict, Iterator, List, Tuple

import z3
from Crypto.Hash import keccak

from common import (
    BW,
    Block,
    ByteArray,
    Instruction,
    IntrospectableArray,
    State,
    do_check,
    goal,
)
from disassembler import disassemble
from vm import execute


def universal_transaction(
    instructions: List[Instruction], jumps: Dict[int, int]
) -> Iterator[Tuple[z3.Solver, State, State]]:
    block = Block(
        number=z3.BitVec("NUMBER", 256),
        coinbase=z3.BitVec("COINBASE", 160),
        timestamp=z3.BitVec("TIMESTAMP", 256),
        prevrandao=z3.BitVec("PREVRANDAO", 256),
        gaslimit=z3.BitVec("GASLIMIT", 256),
        chainid=z3.BitVec("CHAINID", 256),
        basefee=z3.BitVec("BASEFEE", 256),
    )

    start = State(
        jumps=jumps,
        address=z3.BitVec("ADDRESS", 160),
        # TODO: properly constrain ORIGIN to be an EOA and CALLER to either be
        # equal to ORIGIN or else be a non-EOA.
        origin=z3.BitVec("ORIGIN", 160),
        caller=z3.BitVec("CALLER", 160),
        callvalue=z3.BitVec("CALLVALUE", 256),
        calldata=ByteArray("CALLDATA"),
        gasprice=z3.BitVec("GASPRICE", 256),
        # TODO: the balances of other accounts can change between transactions
        # (and the balance of this contract account too, via SELFDESTRUCT). How
        # do we model this?
        balances=IntrospectableArray(
            "BALANCES", z3.BitVecSort(160), z3.BitVecSort(256)
        ),
        storage=IntrospectableArray("STORAGE", z3.BitVecSort(256), z3.BitVecSort(256)),
        contribution=z3.BitVec("CONTRIBUTION", 256),
        extraction=z3.BitVec("EXTRACTION", 256),
    )

    init = start.copy()
    init.transfer_initial()
    states = execute(instructions, block, init)
    while len(states) > 0:
        s = states.pop()

        solver = z3.Optimize()
        s.constrain(solver)
        solver.minimize(s.callvalue)
        solver.minimize(s.calldata.length())
        if do_check(solver):
            if s.success == True:
                # Potential match!
                yield solver, start, s
            elif s.success == False:
                # Ignore executions that REVERT, since they can't affect
                # permanent state.
                pass
            else:
                # Ordinary fork in execution, keep going...
                states += execute(instructions, block, s)
        else:
            # We took an illegal turn at the last JUMPI. This branch is
            # unreachable, ignore it.
            pass


def print_solution(
    solver: z3.Solver,
    start: State,
    end: State,
    *extra: z3.ExprRef,
    debug_key: z3.ExprRef = None,
) -> None:
    assert do_check(solver, *extra)

    if do_check(solver, *goal(start, end), *extra):
        kind = "🚩 GOAL"
        extra = (*extra, *goal(start, end))
    elif end.is_changed(solver, start):
        # This assertion can fail if we give Z3 obviously contradictory
        # constraints :(
        assert len(solver.unsat_core()) > 0
        do_check(solver, *extra)  # reset so we can extract the model
        kind = "📒 STEP"
    else:
        return

    m = solver.model()

    assert end.success == True
    if len(end.returndata) > 0:
        rdata = "0x" + "".join(
            m.eval(b, True).as_long().to_bytes(1, "big").hex() for b in end.returndata
        )
    else:
        rdata = "-"
    print(f"{kind}\t{hex(end.path).replace('0x', 'Px')}\t{rdata}")

    for skey in end.sha3keys:
        key = m.eval(skey, True)
        data = key.as_long().to_bytes(key.size() // 8, "big")
        hash = keccak.new(data=data, digest_bits=256)
        digest = int.from_bytes(hash.digest(), "big")
        solver.assert_and_track(skey == key, "SHAKEY")
        solver.assert_and_track(end.sha3hash[skey.size()][skey] == BW(digest), "SHAVAL")
        assert do_check(solver, *extra)
        m = solver.model()

    value = m.eval(end.callvalue).as_long()
    if value:
        print(f"Value\tETH 0x{value.to_bytes(32, 'big').hex()}")

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
        print(f"Gas\tETH {m.eval(end.gasprice).as_long():011,}")

    print(
        f"Contrib\tETH 0x{m.eval(start.contribution, True).as_long().to_bytes(32, 'big').hex()}"
    )
    print(
        f"\t-> ETH 0x{m.eval(end.contribution, True).as_long().to_bytes(32, 'big').hex()}"
    )
    print(
        f"Extract\tETH 0x{m.eval(start.extraction, True).as_long().to_bytes(32, 'big').hex()}"
    )
    print(
        f"\t-> ETH 0x{m.eval(end.extraction, True).as_long().to_bytes(32, 'big').hex()}"
    )

    print_array("Balance", m, start.balances, end.balances)
    print_array("Storage", m, start.storage, end.storage)
    print()

    if debug_key is not None:
        print(f"Key\t0x{m.eval(debug_key, True).as_long().to_bytes(32, 'big').hex()}")
        print(
            f"Value\t0x{m.eval(start.storage.array[debug_key], True).as_long().to_bytes(32, 'big').hex()}"
        )
        print(
            f"\t-> 0x{m.eval(end.storage.array[debug_key], True).as_long().to_bytes(32, 'big').hex()}"
        )
        print()


def print_array(
    name: str,
    m: z3.Model,
    start: IntrospectableArray,
    end: IntrospectableArray,
) -> None:
    indexify: Callable[[z3.ExprRef], str] = (
        lambda key: f"0x{key.as_long():x}" if z3.is_bv_value(key) else str(key)
    )
    valueify: Callable[[z3.ExprRef], str] = lambda val: f"0x{val.as_long():x}"

    accesses = {}
    for sym in end.accessed:
        key = indexify(m.eval(sym))
        val = valueify(m.eval(start.array[sym], True))
        accesses[key] = val

    writes = {}
    for sym in end.written:
        key = indexify(m.eval(sym))
        pre = valueify(m.eval(start.array[sym], True))
        post = valueify(m.eval(end.array[sym], True))
        writes[key] = (pre, post)

    if len(accesses) > 0 or len(writes) > 0:
        print(name, end="")
        for key in sorted(accesses.keys()):
            print(f"\tR: {key} ", end="")
            if len(key) > 16:
                print("\n\t", end="")
            print(f"-> {accesses[key]}")
        for key in sorted(writes.keys()):
            print(f"\tW: {key} ", end="")
            if len(key) > 16:
                print("\n\t", end="")
            pre, post = writes[key]
            print(f"-> {post} ", end="")
            if len(post) > 16:
                print("\n\t   ", end="")
            if pre == post:
                print(f"(no change)")
            else:
                print(f"(from {pre})")


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    for solver, start, end in universal_transaction(instructions, jumps):
        print_solution(solver, start, end)

    print("End Universal Transaction")
