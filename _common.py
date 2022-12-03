from typing import Callable, Optional, cast

import z3

from state import State
from symbolic import BW, Array, check, concretize, concretize_hex, solver_stack


class Predicate:
    def __init__(
        self,
        expression: Callable[[State], z3.ExprRef],
        description: str,
        state: State,
        storage_key: Optional[z3.ExprRef] = None,
    ) -> None:
        self.expression = expression
        self.description = description
        self.state = state
        self.storage_key = storage_key

    def eval(self, state: State) -> z3.ExprRef:
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


def _eval(
    model: z3.ModelRef, t: z3.ExprRef, model_completion: bool = False
) -> z3.BitVecRef:
    if not z3.is_bv(t):
        raise ValueError("unexpected non-bitvector")
    return cast(z3.BitVecRef, model.eval(t, model_completion))


def _print_solution(
    kind: str,
    solver: z3.Optimize,
    start: State,
    end: State,
    predicate: Optional[Predicate] = None,
) -> None:
    m = solver.model()

    assert end.success is True
    if len(end.returndata) > 0:
        rdata = "0x" + "".join(
            concretize_hex(_eval(m, b, True)) for b in end.returndata
        )
    else:
        rdata = "-"
    print(f"{kind}\t{hex(end.path).replace('0x', 'Px')}\t{rdata}")

    m = end.sha3.concretize(solver, m)
    if predicate is not None:
        # TODO: this should be redundant now
        m = predicate.state.sha3.concretize(solver, m)

    if concretize(_eval(m, end.callvalue)):
        print(f"Value\tETH 0x{concretize_hex(_eval(m, end.callvalue))}")

    print(f"Data\t({_eval(m, end.calldata.length())}) 0x", end="")
    for i in range(concretize(_eval(m, end.calldata.length()))):
        b = _eval(m, end.calldata.get(BW(i)))
        if z3.is_bv_value(b):
            print(concretize_hex(b), end="")
        else:
            print("??", end="")
        if i == 3:
            print(" ", end="")
    print()
    if z3.is_bv_value(_eval(m, end.address)):
        print(f"Address\t0x{concretize_hex(_eval(m, end.address))}")
    if z3.is_bv_value(_eval(m, end.caller)):
        print(f"Caller\t0x{concretize_hex(_eval(m, end.caller))}")
    if z3.is_bv_value(_eval(m, end.gasprice)):
        print(f"Gas\tETH {concretize(_eval(m, end.gasprice)):011,}")

    cs = concretize(_eval(m, start.universe.contribution, True))
    ce = concretize(_eval(m, end.universe.contribution, True))
    es = concretize(_eval(m, start.universe.extraction, True))
    ee = concretize(_eval(m, end.universe.extraction, True))
    if cs != ce:
        print(f"Contrib\tETH 0x{concretize_hex(BW(cs))}")
        print(f"\t-> ETH 0x{concretize_hex(BW(ce))}")
    if es != ee:
        print(f"Extract\tETH 0x{concretize_hex(BW(es))}")
        print(f"\t-> ETH 0x{concretize_hex(BW(ee))}")

    print_array("Balance", m, start.universe.balances, end.universe.balances)
    print_array("Storage", m, start.contract.storage, end.contract.storage)
    print()

    if predicate is not None and predicate.storage_key is not None:
        print(f"Key\t0x{concretize_hex(_eval(m, predicate.storage_key, True))}")
        print(
            f"Value\t0x{concretize_hex(_eval(m, start.contract.storage.array[predicate.storage_key], True))}"
        )
        print(
            f"\t-> 0x{concretize_hex(_eval(m, end.contract.storage.array[predicate.storage_key], True))}"
        )
        print()


def print_array(
    name: str,
    m: z3.ModelRef,
    start: Array,
    end: Array,
) -> None:
    indexify: Callable[[z3.ExprRef], str] = (
        lambda key: f"0x{concretize(key):x}" if z3.is_bv_value(key) else str(key)
    )
    valueify: Callable[[z3.ExprRef], str] = lambda val: f"0x{concretize(val):x}"

    accesses = {}
    for sym in end.accessed:
        key = indexify(_eval(m, sym))
        val = valueify(_eval(m, start.array[sym], True))
        accesses[key] = val

    writes = {}
    for sym in end.written:
        key = indexify(_eval(m, sym))
        pre = valueify(_eval(m, start.array[sym], True))
        post = valueify(_eval(m, end.array[sym], True))
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
