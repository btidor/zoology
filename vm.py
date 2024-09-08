"""A machine to execute compiled symbolic programs."""

from __future__ import annotations

import copy
from heapq import heappop, heappush
from typing import Iterable

from bytes import Bytes
from compiler import (
    HyperGlobal,
    HyperInvoke,
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
    address = Address.unwrap(tx.address, "execute")
    if address not in k.contracts:
        # CALLing an EOA always returns success. This includes DELEGATECALL!
        yield k, Terminus(Path(), (), True, Bytes(), None)
        return
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
                    heappush(queue, (r0, k))
                    # We have to maintain this invariant so that modifications
                    # to r.storage are reflected in k.contracts.
                    k = copy.deepcopy(k)
                    k.contracts[address].storage = r1.storage
                    heappush(queue, (r1, k))
                    break
                case TerminateOp(success, returndata):
                    storage = r.storage if success and not r.path.static else None
                    terminus = Terminus(r.path, (), success, returndata, storage)
                    yield k, terminus
                    break
                case CreateOp() as op:
                    created, subtx, override = op.before(k, tx, r.path)
                    for k, term in execute(k, subtx, block, override):
                        assert term.path.constraint.reveal() is True
                        if term.success:
                            k.contracts[created].program = disassemble(term.returndata)
                            op.after(r, Uint160(created))
                        else:
                            del k.contracts[created]
                            op.after(r, Uint160(0))
                        # That invariant again...
                        r.storage = k.contracts[address].storage
                        heappush(queue, (r, k))
                    break
                case CallOp() as op:
                    _, subtx, override = op.before(k, tx, r.path)
                    for k, term in execute(k, subtx, block, override):
                        assert term.path.constraint.reveal() is True
                        if op.static:
                            assert term.path.static, "STATICCALL executed non-static op"
                        op.after(r, Constraint(term.success), term.returndata)
                        # That invariant again...
                        r.storage = k.contracts[address].storage
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
                case HyperInvoke():
                    for k, delta in _invoke(hyper, k, tx, block, term.path):
                        next.append((k, term.substitute(delta)))
        terms = next
    return terms


def _global(h: HyperGlobal, k: Blockchain) -> Substitutions:
    input = [k if arg is None else arg for arg in h.op.input]
    result = h.op.fn(*input)
    assert isinstance(result, Uint)
    return [(h.placeholder, result)]


def _invoke(
    h: HyperInvoke, k: Blockchain, tx: Transaction, block: Block, path: Path
) -> Iterable[tuple[Blockchain, Substitutions]]:
    sender = Address.unwrap(tx.address)
    before, after = h.storage
    k.contracts[sender].storage = before

    address, subtx, override = h.op.before(k, tx, path)
    for k, term in execute(k, subtx, block, override):
        if isinstance(h.op, CreateOp):
            if term.success:
                k.contracts[address].program = disassemble(term.returndata)
            else:
                del k.contracts[address]
            assert isinstance(h.placeholder, Uint)
            delta: Substitutions = [
                (h.placeholder, Uint160(address if term.success else 0))
            ]
        else:
            if h.op.static:
                assert term.path.static, "STATICCALL executed non-static op"
            assert isinstance(h.placeholder, tuple)
            success, returndata = h.placeholder
            delta: Substitutions = [
                (success, Constraint(term.success)),
                *substitutions(returndata, term.returndata),
            ]

        delta.append((after, k.contracts[sender].storage))
        yield k, delta
