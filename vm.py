"""A machine to execute compiled symbolic programs."""

import copy

from bytes import Bytes
from compiler import compile, symbolic_block, symbolic_transaction
from disassembler import Program, disassemble
from ops import CreateOp, ForkOp, HyperCall, HyperCreate, HyperGlobal, TerminateOp, step
from path import Path
from smt import (
    Array,
    Constraint,
    Substitutions,
    Uint160,
    Uint256,
    substitute,
    substitutions,
)
from state import (
    Address,
    Block,
    Blockchain,
    Runtime,
    Terminus,
    Transaction,
)


def interpret(
    k: Blockchain, tx: Transaction, program: Program | None = None
) -> tuple[Blockchain, Terminus]:
    """Interpret a program with concrete inputs."""
    block, address = Block(), Address.unwrap(tx.address, "interpret")
    if program is None:
        program = k.contracts[address].program

    r = Runtime(program=program, storage=k.contracts[address].storage)
    while True:
        result = step(r, k, tx, block)
        if r.hyper:
            assert len(r.hyper) == 1
            match hyper := r.hyper[0]:
                case HyperGlobal():
                    raise NotImplementedError
                case HyperCreate():
                    raise NotImplementedError
                case HyperCall():
                    k, delta, _ = hypercall(hyper, k, tx)
            r = r.substitute(delta)
            result = substitute(result, delta)
            r.hyper.clear()

        match result:
            case None:
                pass
            case ForkOp(r0, r1):
                a = r0.path.constraint.reveal()
                b = r1.path.constraint.reveal()
                match (a, b):
                    case (True, False):
                        r = r0
                    case (False, True):
                        r = r1
                    case _:
                        raise ValueError(f"expected one concrete path, got {(a, b)}")
            case TerminateOp(success, returndata):
                storage = r.storage if success and not r.path.static else None
                terminus = Terminus(
                    r.path, tuple(r.hyper), success, returndata, storage
                )
                return k, terminus
            case CreateOp() as op:
                address, subtx, override = op.before(k, tx, r.path)
                k, term = interpret(k, subtx, override)
                assert term.path.constraint.reveal() is True

                if term.success:
                    k.contracts[address].program = disassemble(term.returndata)
                    op.after(r, Uint160(address))
                else:
                    del k.contracts[address]
                    op.after(r, Uint160(address))
            case _:
                raise NotImplementedError


def execute(
    ki: Blockchain, tx: Transaction, program: Program | None = None
) -> tuple[Blockchain, Terminus]:
    """Compile and execute a program with concrete inputs."""
    # TODO: `execute` will always be slower than `interpret` until
    # compile-sharing is implemented.

    block, address = Block(), Address.unwrap(tx.address, "apply")
    if program is None:
        program = ki.contracts[address].program

    subs = [
        *substitutions(symbolic_block(), block),
        *substitutions(symbolic_transaction(), tx),
        (Array[Uint256, Uint256]("STORAGE"), ki.contracts[address].storage),
    ]

    for term in compile(program):
        k = copy.deepcopy(ki)
        term = term.substitute(subs)

        for i in range(len(term.hyper)):
            hyper = term.hyper[i]
            match hyper:
                case HyperGlobal():
                    delta, ok = hyperglobal(hyper, k), Constraint(True)
                case HyperCreate():
                    k, delta, ok = hypercreate(hyper, k, tx, term.path)
                case HyperCall():
                    k, delta, ok = hypercall(hyper, k, tx)
            term = term.substitute(delta)
            term.path.constraint &= ok

        assert (ok := term.path.constraint.reveal()) is not None
        if ok:
            if term.storage:
                k.contracts[address].storage = term.storage
            return k, term

    raise RuntimeError("no termination matched")


def hyperglobal(h: HyperGlobal, k: Blockchain) -> Substitutions:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.input]
    result = h.fn(*input)
    return [(h.result, result)]


def hypercreate(
    h: HyperCreate, k: Blockchain, tx: Transaction, path: Path
) -> tuple[Blockchain, Substitutions, Constraint]:
    """Simulate a concrete CREATE hypercall."""
    sender = Address.unwrap(tx.address, "CREATE/CREATE2")
    before, after = h.storage
    k.contracts[sender].storage = before

    address, subtx, override = h.op.before(k, tx, path)
    k, t = interpret(k, subtx, override)
    if t.success:
        k.contracts[address].program = disassemble(t.returndata)
    else:
        del k.contracts[address]

    return (
        k,
        [
            (h.address, Uint160(address if t.success else 0)),
            (after, k.contracts[sender].storage),
        ],
        Constraint(True),
    )


def hypercall(
    h: HyperCall, k: Blockchain, tx: Transaction
) -> tuple[Blockchain, Substitutions, Constraint]:
    """Simulate a concrete CALL, etc. hypercall."""
    sender = Address.unwrap(tx.address, "CALL/DELEGATECALL/STATICCALL")
    address = Address.unwrap(h.address, "CALL/DELEGATECALL/STATICCALL")
    assert (calldata := h.calldata.reveal()) is not None
    tx = Transaction(
        origin=tx.origin,
        caller=tx.caller if h.delegate else tx.address,
        address=tx.address if h.delegate else h.address,
        callvalue=h.callvalue,
        calldata=Bytes(calldata),
        gasprice=tx.gasprice,
    )
    before, after = h.storage
    k.contracts[sender].storage = before
    if not h.delegate:
        ok = k.transfer(tx.caller, tx.address, h.callvalue)
    else:
        ok = Constraint(True)

    if address in k.contracts:
        program = k.contracts[address].program if h.delegate else None
        k, t = interpret(k, tx, program)
        if h.static:
            assert t.path.static, "STATICCALL executed non-static op"
        constraint, returndata = Constraint(t.success), t.returndata
    else:
        constraint, returndata = Constraint(True), Bytes()

    return (
        k,
        [
            (h.success, constraint),
            *substitutions(h.returndata, returndata),
            *(((after, k.contracts[sender].storage),) if after else ()),
        ],
        ok,
    )
