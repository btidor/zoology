from typing import Callable, Optional

import z3

from state import State
from symbolic import (
    BW,
    Array,
    check,
    is_concrete,
    solver_stack,
    unwrap,
    unwrap_bytes,
    zeval,
)


class Predicate:
    def __init__(
        self,
        expression: Callable[[State], z3.BoolRef],
        description: str,
        state: State,
        storage_key: Optional[z3.BitVecRef] = None,
    ) -> None:
        self.expression = expression
        self.description = description
        self.state = state
        self.storage_key = storage_key

    def eval(self, state: State) -> z3.BoolRef:
        return self.expression(state)

    def __repr__(self) -> str:
        return self.description


def print_solution(
    start: State,
    end: State,
    predicate: Optional[Predicate] = None,
) -> None:
    solver = z3.Optimize()
    end.constrain(solver, minimize=True)
    assert check(solver)

    with solver_stack(solver):
        constrain_to_goal(solver, start, end)
        if check(solver):
            _print_solution("🚩 GOAL", solver, start, end, predicate)
            return

        # `do_check()` can incorrectly return false if we give Z3 obviously
        # contradictory constraints :(
        assert len(solver.unsat_core()) > 0

    if end.is_changed(solver, start):
        check(solver)  # reset so we can extract the model
        _print_solution("📒 STEP", solver, start, end, predicate)


def _print_solution(
    kind: str,
    solver: z3.Optimize,
    start: State,
    end: State,
    predicate: Optional[Predicate] = None,
) -> None:
    m = solver.model()

    assert end.success is True
    returnlen = unwrap(end.returndata.length())
    if returnlen > 0:
        rdata = "0x" + "".join(
            unwrap_bytes(zeval(m, end.returndata[BW(i)], True)).hex()
            for i in range(returnlen)
        )
    else:
        rdata = "-"
    print(f"{kind}\t{hex(end.path).replace('0x', 'Px')}\t{rdata}")

    m = end.sha3.narrow(solver, m)
    if predicate is not None:
        # TODO: this should be redundant now
        m = predicate.state.sha3.narrow(solver, m)

    if unwrap(zeval(m, end.callvalue)) > 0:
        print(f"Value\tETH 0x{unwrap_bytes(zeval(m, end.callvalue)).hex()}")

    print(f"Data\t({zeval(m, end.calldata.length())}) 0x", end="")
    for i in range(unwrap(zeval(m, end.calldata.length()))):
        b = zeval(m, end.calldata[BW(i)])
        if z3.is_bv_value(b):
            print(unwrap_bytes(b).hex(), end="")
        else:
            print("??", end="")
        if i == 3:
            print(" ", end="")
    print()
    if z3.is_bv_value(zeval(m, end.address)):
        print(f"Address\t0x{unwrap_bytes(zeval(m, end.address)).hex()}")
    if z3.is_bv_value(zeval(m, end.caller)):
        print(f"Caller\t0x{unwrap_bytes(zeval(m, end.caller)).hex()}")
    if z3.is_bv_value(zeval(m, end.gasprice)):
        print(f"Gas\tETH {unwrap(zeval(m, end.gasprice)):011,}")

    cs = unwrap(zeval(m, start.universe.contribution, True))
    ce = unwrap(zeval(m, end.universe.contribution, True))
    es = unwrap(zeval(m, start.universe.extraction, True))
    ee = unwrap(zeval(m, end.universe.extraction, True))
    if cs != ce:
        print(f"Contrib\tETH 0x{unwrap_bytes(BW(cs)).hex()}")
        print(f"\t-> ETH 0x{unwrap_bytes(BW(ce)).hex()}")
    if es != ee:
        print(f"Extract\tETH 0x{unwrap_bytes(BW(es)).hex()}")
        print(f"\t-> ETH 0x{unwrap_bytes(BW(ee)).hex()}")

    print_array("Balance", m, start.universe.balances, end.universe.balances)
    print_array("Storage", m, start.contract.storage, end.contract.storage)
    print()

    if predicate is not None and predicate.storage_key is not None:
        print(f"Key\t0x{unwrap_bytes(zeval(m, predicate.storage_key, True)).hex()}")
        print(
            f"Value\t0x{unwrap_bytes(zeval(m, start.contract.storage.peek(predicate.storage_key), True)).hex()}"
        )
        print(
            f"\t-> 0x{unwrap_bytes(zeval(m, end.contract.storage.peek(predicate.storage_key), True)).hex()}"
        )
        print()


def print_array(
    name: str,
    m: z3.ModelRef,
    start: Array,
    end: Array,
) -> None:
    indexify: Callable[[z3.BitVecRef], str] = (
        lambda key: f"0x{unwrap(key):x}" if is_concrete(key) else str(key)
    )
    valueify: Callable[[z3.BitVecRef], str] = lambda val: f"0x{unwrap(val):x}"

    accesses = {}
    for sym in end.accessed:
        key = indexify(zeval(m, sym))
        val = valueify(zeval(m, start.peek(sym), True))
        accesses[key] = val

    writes = {}
    for sym in end.written:
        key = indexify(zeval(m, sym))
        pre = valueify(zeval(m, start.peek(sym), True))
        post = valueify(zeval(m, end.peek(sym), True))
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


def constrain_to_goal(solver: z3.Optimize, start: State, end: State) -> None:
    solver.assert_and_track(
        z3.ULT(start.universe.extraction, start.universe.contribution), "GOAL.PRE"
    )
    solver.assert_and_track(
        z3.UGT(end.universe.extraction, end.universe.contribution), "GOAL.POST"
    )
