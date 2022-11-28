#!/usr/bin/env python3

from typing import Callable, Dict, Iterator, List, Optional, Tuple

import z3
from Crypto.Hash import keccak

from common import (
    BW,
    Block,
    ByteArray,
    Instruction,
    IntrospectableArray,
    Predicate,
    State,
    do_check,
    goal,
    hexify,
)
from disassembler import disassemble
from vm import execute


def make_start(jumps: Dict[int, int], suffix: str = "") -> Tuple[Block, State]:
    block = Block(
        number=z3.BitVec(f"NUMBER{suffix}", 256),
        coinbase=z3.BitVec(f"COINBASE{suffix}", 160),
        timestamp=z3.BitVec(f"TIMESTAMP{suffix}", 256),
        prevrandao=z3.BitVec(f"PREVRANDAO{suffix}", 256),
        gaslimit=z3.BitVec(f"GASLIMIT{suffix}", 256),
        chainid=z3.BitVec(f"CHAINID", 256),
        basefee=z3.BitVec(f"BASEFEE{suffix}", 256),
    )
    start = State(
        suffix=suffix,
        jumps=jumps,
        address=z3.BitVec("ADDRESS", 160),
        # TODO: properly constrain ORIGIN to be an EOA and CALLER to either be
        # equal to ORIGIN or else be a non-EOA; handle the case where ORIGIN and
        # CALLER vary across transactions.
        origin=z3.BitVec(f"CALLER", 160),
        caller=z3.BitVec(f"CALLER", 160),
        callvalue=z3.BitVec(f"CALLVALUE{suffix}", 256),
        calldata=ByteArray(f"CALLDATA{suffix}"),
        gasprice=z3.BitVec(f"GASPRICE{suffix}", 256),
        storage=IntrospectableArray(
            f"STORAGE{suffix}", z3.BitVecSort(256), z3.BitVecSort(256)
        ),
        # TODO: the balances of other accounts can change between transactions
        # (and the balance of this contract account too, via SELFDESTRUCT). How
        # do we model this?
        balances=IntrospectableArray(
            f"BALANCES{suffix}", z3.BitVecSort(160), z3.BitVecSort(256)
        ),
        contribution=z3.BitVec(f"CONTRIBUTION{suffix}", 256),
        extraction=z3.BitVec(f"EXTRACTION{suffix}", 256),
    )
    return block, start


def universal_transaction(
    block: Block, start: State, instructions: List[Instruction]
) -> Iterator[Tuple[z3.Solver, State]]:

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
                yield solver, s
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
    predicate: Optional[Predicate] = None,
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
        rdata = "0x" + "".join(hexify(m.eval(b, True), 1) for b in end.returndata)
    else:
        rdata = "-"
    print(f"{kind}\t{hex(end.path).replace('0x', 'Px')}\t{rdata}")

    m = narrow_sha3(solver, m, end, extra)
    if predicate is not None:
        m = narrow_sha3(solver, m, predicate.state, extra)

    if m.eval(end.callvalue).as_long():
        print(f"Value\tETH 0x{hexify(m.eval(end.callvalue), 32)}")

    print(f"Data\t({m.eval(end.calldata.length())}) 0x", end="")
    for i in range(m.eval(end.calldata.length()).as_long()):
        b = m.eval(end.calldata.get(i))
        if z3.is_bv_value(b):
            print(hexify(b, 1), end="")
        else:
            print("??", end="")
        if i == 3:
            print(" ", end="")
    print()
    if z3.is_bv_value(m.eval(end.address)):
        print(f"Address\t0x{hexify(m.eval(end.address), 20)}")
    if z3.is_bv_value(m.eval(end.caller)):
        print(f"Caller\t0x{hexify(m.eval(end.caller), 20)}")
    if z3.is_bv_value(m.eval(end.gasprice)):
        print(f"Gas\tETH {m.eval(end.gasprice).as_long():011,}")

    cs, ce = m.eval(start.contribution, True), m.eval(end.contribution, True)
    es, ee = m.eval(start.extraction, True), m.eval(end.extraction, True)
    if cs.as_long() != ce.as_long():
        print(f"Contrib\tETH 0x{hexify(cs, 32)}")
        print(f"\t-> ETH 0x{hexify(ce, 32)}")
    if es.as_long() != ee.as_long():
        print(f"Extract\tETH 0x{hexify(es, 32)}")
        print(f"\t-> ETH 0x{hexify(ee, 32)}")

    print_array("Balance", m, start.balances, end.balances)
    print_array("Storage", m, start.storage, end.storage)
    print()

    if predicate is not None and predicate.storage_key is not None:
        print(f"Key\t0x{hexify(m.eval(predicate.storage_key, True),32)}")
        print(
            f"Value\t0x{hexify(m.eval(start.storage.array[predicate.storage_key], True),32)}"
        )
        print(
            f"\t-> 0x{hexify(m.eval(end.storage.array[predicate.storage_key], True),32)}"
        )
        print()


def narrow_sha3(
    solver: z3.Solver, model: z3.Model, state: State, extra: Tuple[z3.ExprRef, ...]
) -> z3.Model:
    hashes: Dict[bytes, bytes] = {}
    for i, skey in enumerate(state.sha3keys):
        ckey = model.eval(skey, True)
        data = ckey.as_long().to_bytes(ckey.size() // 8, "big")
        hash = keccak.new(data=data, digest_bits=256)
        digest = int.from_bytes(hash.digest(), "big")
        hashes[data] = hash.digest()
        solver.assert_and_track(skey == ckey, f"SHAKEY{i}{state.suffix}")
        solver.assert_and_track(
            state.sha3hash[skey.size()][skey] == BW(digest),
            f"SHAVAL{i}{state.suffix}",
        )
        assert do_check(solver, *extra)
        model = solver.model()

    if len(hashes) > 0:
        print(f"SHA3{state.suffix}", end="")
        keys = sorted(hashes.keys())
        for k in keys:
            if len(k) == 64:
                a = hex(int.from_bytes(k[:32], "big"))
                b = hex(int.from_bytes(k[32:], "big"))
                sk = f"0x[{a[2:]}.{b[2:]}]"
            else:
                sk = hex(int.from_bytes(k, "big"))
            print(f"\t{sk} ", end="")
            if len(sk) > 34:
                print("\n\t", end="")
            print(f"-> 0x{hashes[k].hex()}")

    return model


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
            if len(key) > 34:
                print("\n\t", end="")
            print(f"-> {accesses[key]}")
        for key in sorted(writes.keys()):
            print(f"\tW: {key} ", end="")
            if len(key) > 34:
                print("\n\t", end="")
            pre, post = writes[key]
            print(f"-> {post} ", end="")
            if len(post) > 34:
                print("\n\t   ", end="")
            print(f"(no change)" if pre == post else f"(from {pre})")


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    block, start = make_start(jumps)
    for solver, end in universal_transaction(block, start, instructions):
        print_solution(solver, start, end)

    print("End Universal Transaction")
