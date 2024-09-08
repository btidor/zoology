"""A machine to execute compiled symbolic programs."""

from __future__ import annotations

from heapq import heappop, heappush
from typing import Iterable

from bytes import Bytes
from compiler import (
    HyperCall,
    HyperCreate,
    HyperGlobal,
    Terminus,
)
from disassembler import Program, disassemble
from environ import (
    Address,
    Block,
    Blockchain,
    Runtime,
    Transaction,
)
from ops import (
    CallOp,
    CreateOp,
    ForkOp,
    TerminateOp,
    step,
)
from path import Path
from smt import (
    Constraint,
    Substitutions,
    Uint,
    Uint160,
    substitutions,
)


def execute(
    k: Blockchain,
    tx: Transaction,
    block: Block | None = None,
    override: Program | None = None,
) -> Iterable[tuple[Blockchain, Terminus]]:
    """Interpret a program with concrete inputs."""
    block = block or Block()
    address = Address.unwrap(tx.address, "interpret")
    program = override or k.contracts[address].program
    r = Runtime(program=program, storage=k.contracts[address].storage)

    queue = list[tuple[Runtime, Blockchain]]([(r, k)])
    while queue:
        r, k = heappop(queue)
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
                            raise ValueError(
                                f"expected one concrete path, got {(a, b)}"
                            )
                case TerminateOp(success, returndata):
                    storage = r.storage if success and not r.path.static else None
                    terminus = Terminus(r.path, (), success, returndata, storage)
                    yield k, terminus
                    break
                case CreateOp() as op:
                    address, subtx, override = op.before(k, tx, r.path)
                    for k, term in execute(k, subtx, block, override):
                        assert term.path.constraint.reveal() is True
                        if term.success:
                            k.contracts[address].program = disassemble(term.returndata)
                            op.after(r, Uint160(address))
                        else:
                            del k.contracts[address]
                            op.after(r, Uint160(address))
                        heappush(queue, (r, k))
                    break
                case CallOp() as op:
                    address, subtx, override = op.before(k, tx, r.path)
                    for k, term in execute(k, subtx, block, override):
                        assert term.path.constraint.reveal() is True
                        if op.static:
                            assert term.path.static, "STATICCALL executed non-static op"
                        op.after(r, Constraint(term.success), term.returndata)
                        heappush(queue, (r, k))
                    break


def handle_hypercalls(
    k: Blockchain, tx: Transaction, block: Block, term: Terminus
) -> Iterable[tuple[Blockchain, Terminus]]:
    """Simulate hypercalls using the current global state."""
    n = len(term.hyper)
    terms = [(k, term)]
    for i in range(n):
        next = list[tuple[Blockchain, Terminus]]()
        for k, term in terms:
            hyper = term.hyper[i]
            match hyper:
                case HyperGlobal():
                    delta = _global(hyper, k)
                    next.append((k, term.substitute(delta)))
                case HyperCreate():
                    for k, delta in _create(hyper, k, tx, block, term.path):
                        next.append((k, term.substitute(delta)))
                case HyperCall():
                    for k, delta in _call(hyper, k, tx, block, term.path):
                        next.append((k, term.substitute(delta)))
        terms = next
    return terms


def _global(h: HyperGlobal, k: Blockchain) -> Substitutions:
    input = [k if arg is None else arg for arg in h.op.input]
    result = h.op.fn(*input)
    assert isinstance(result, Uint)
    return [(h.result, result)]


def _create(
    h: HyperCreate, k: Blockchain, tx: Transaction, block: Block, path: Path
) -> Iterable[tuple[Blockchain, Substitutions]]:
    sender = Address.unwrap(tx.address, "CREATE/CREATE2")
    before, after = h.storage
    k.contracts[sender].storage = before

    address, subtx, override = h.op.before(k, tx, path)
    for k, t in execute(k, subtx, block, override):
        if t.success:
            k.contracts[address].program = disassemble(t.returndata)
        else:
            del k.contracts[address]

        subs: Substitutions = [
            (h.address, Uint160(address if t.success else 0)),
            (after, k.contracts[sender].storage),
        ]
        yield k, subs


def _call(
    h: HyperCall, k: Blockchain, tx: Transaction, block: Block, path: Path
) -> Iterable[tuple[Blockchain, Substitutions]]:
    sender = Address.unwrap(tx.address, "CALL/DELEGATECALL/STATICCALL")
    before, after = h.storage
    k.contracts[sender].storage = before

    address, subtx, override = h.op.before(k, tx, path)
    if address in k.contracts:
        for k, t in execute(k, subtx, block, override):
            if h.op.static:
                assert t.path.static, "STATICCALL executed non-static op"
            subs: Substitutions = [
                (h.success, Constraint(t.success)),
                *substitutions(h.returndata, t.returndata),
                *(((after, k.contracts[sender].storage),) if after else ()),
            ]
            yield k, subs
    else:
        subs: Substitutions = [
            (h.success, Constraint(True)),
            *substitutions(h.returndata, Bytes()),
            *(((after, k.contracts[sender].storage),) if after else ()),
        ]
        yield k, subs
