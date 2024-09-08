"""A machine to execute compiled symbolic programs."""

import copy

from bytes import Bytes
from compiler import compile, symbolic_block, symbolic_transaction
from disassembler import Program, disassemble
from ops import (
    CallOp,
    CreateOp,
    ForkOp,
    HyperCall,
    HyperCreate,
    HyperGlobal,
    TerminateOp,
    step,
)
from path import Path
from smt import (
    Array,
    Constraint,
    Substitutions,
    Uint,
    Uint160,
    Uint256,
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
        match step(r, k, tx, block):
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
            case CallOp() as op:
                address, subtx, override = op.before(k, tx, r.path)
                k, term = interpret(k, subtx, override)
                assert term.path.constraint.reveal() is True

                if op.static:
                    assert term.path.static, "STATICCALL executed non-static op"
                op.after(r, Constraint(term.success), term.returndata)


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
                    k, delta = hypercreate(hyper, k, tx, term.path)
                case HyperCall():
                    k, delta = hypercall(hyper, k, tx, term.path)
            term = term.substitute(delta)

        assert (ok := term.path.constraint.reveal()) is not None
        if ok:
            if term.storage:
                k.contracts[address].storage = term.storage
            return k, term

    raise RuntimeError("no termination matched")


def hyperglobal(h: HyperGlobal, k: Blockchain) -> Substitutions:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.op.input]
    result = h.op.fn(*input)
    assert isinstance(result, Uint)
    return [(h.result, result)]


def hypercreate(
    h: HyperCreate, k: Blockchain, tx: Transaction, path: Path
) -> tuple[Blockchain, Substitutions]:
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

    subs: Substitutions = [
        (h.address, Uint160(address if t.success else 0)),
        (after, k.contracts[sender].storage),
    ]
    return k, subs


def hypercall(
    h: HyperCall, k: Blockchain, tx: Transaction, path: Path
) -> tuple[Blockchain, Substitutions]:
    """Simulate a concrete CALL, etc. hypercall."""
    sender = Address.unwrap(tx.address, "CALL/DELEGATECALL/STATICCALL")
    before, after = h.storage
    k.contracts[sender].storage = before

    address, subtx, override = h.op.before(k, tx, path)
    if address in k.contracts:
        k, t = interpret(k, subtx, override)
        if h.op.static:
            assert t.path.static, "STATICCALL executed non-static op"
        constraint, returndata = Constraint(t.success), t.returndata
    else:
        constraint, returndata = Constraint(True), Bytes()

    subs: Substitutions = [
        (h.success, constraint),
        *substitutions(h.returndata, returndata),
        *(((after, k.contracts[sender].storage),) if after else ()),
    ]
    return k, subs
