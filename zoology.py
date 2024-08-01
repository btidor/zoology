"""A solver for the Ethernaut CTF."""

import copy
from typing import Iterable

from bytes import Bytes
from compiler import compile, symbolic_block, symbolic_transaction
from disassembler import abiencode
from smt import Array, Constraint, Solver, Uint8, Uint160, Uint256, substitutions
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import (
    Address,
    Block,
    Blockchain,
    HyperCall,
    HyperCreate,
    HyperGlobal,
    Terminus,
    Transaction,
)
from vm import execute, hypercall, hypercreate, hyperglobal

PLAYER = 0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0
PROXY = 0xCACACACACACACACACACACACACACACACACACACACA


def load_level(level: int) -> tuple[Blockchain, Address]:
    """Run createInstance() to set up the level."""
    factory = LEVEL_FACTORIES[level]
    k = snapshot_contracts(factory)
    tx = Transaction(
        address=Uint160(factory),
        callvalue=Uint256(10**15),
        calldata=Bytes(abiencode("createInstance(address)") + PLAYER.to_bytes(32)),
    )
    k.balances[tx.address] = Uint256(10**15)

    k, term = execute(k, tx)
    assert (data := term.returndata.reveal()) is not None
    assert term.success, data

    return k, Address(int.from_bytes(data))


def search(level: int, depth: int = 10) -> Iterable[str]:
    """Symbolically execute the given level until a solution is found."""
    FACTORY = LEVEL_FACTORIES[level]
    k, LEVEL = load_level(level)

    block = Block()  # TODO
    vx = Transaction(
        address=Uint160(FACTORY),
        calldata=Bytes(
            abiencode("validateInstance(address,address)")
            + FACTORY.to_bytes(32)
            + PLAYER.to_bytes(32)
        ),
    )
    subs = [
        *substitutions(symbolic_block(), block),
        *substitutions(symbolic_transaction(), vx),
        (Array[Uint256, Uint256]("STORAGE"), k.contracts[FACTORY].storage),
    ]

    solver = Solver()
    validators = list[Terminus]()
    for term in compile(k.contracts[FACTORY].program):
        if not term.success:
            continue

        term = term.substitute(subs)
        term.path.constraint &= term.returndata[Uint256(31)] == Uint8(1)
        if not solver.check(term.path.constraint):
            continue
        validators.append(term)  # TODO: apply hypercalls later...
    assert len(validators) == 1
    validator = validators[0]

    mutations = list[tuple[Address, Terminus]]()
    for address, contract in k.contracts.items():
        if address == FACTORY:
            continue
        mutations.extend((address, t) for t in compile(contract.program) if t.storage)

    for address, mutation in mutations:
        val = validator
        k = copy.deepcopy(k)
        tx = Transaction(
            origin=Uint160(PLAYER),
            caller=Constraint("CALLERAB").ite(Uint160(PLAYER), Uint160(PROXY)),
            address=Uint160(address),
            callvalue=Uint256("CALLVALUE"),
            calldata=Bytes.symbolic("CALLDATA"),
            gasprice=Uint256(0x12),
        )
        mutation = mutation.substitute(
            [
                *substitutions(symbolic_transaction(), tx),
                *substitutions(symbolic_block(), block),  # TODO: increment
                (
                    Array[Uint256, Uint256]("STORAGE"),
                    k.contracts[address].storage,
                ),
            ]
        )
        for i in range(len(mutation.hyper)):
            hyper = mutation.hyper[i]
            match hyper:
                case HyperGlobal():
                    k, delta, ok = hyperglobal(hyper, k, tx, mutation)
                case HyperCreate():
                    k, delta, ok = hypercreate(hyper, k, tx, mutation)
                case HyperCall():
                    k, delta, ok = hypercall(hyper, k, tx, mutation)
            mutation.path.constraint &= ok
            mutation = mutation.substitute(delta)

        for i in range(len(val.hyper)):
            hyper = val.hyper[i]
            match hyper:
                case HyperGlobal():
                    k, delta, ok = hyperglobal(hyper, k, vx, validator)
                case HyperCreate():
                    k, delta, ok = hypercreate(hyper, k, vx, validator)
                case HyperCall():
                    k, delta, ok = hypercall(hyper, k, vx, validator)
            val.path.constraint &= ok

        final = mutation.path.constraint & val.path.constraint
        if solver.check(final):
            solver.add(final)
            for i in range(256):
                c = tx.calldata.length == Uint256(i)
                if solver.check(c):
                    solver.add(c)
                    assert solver.check()
                    break

            # TODO: `mutation.path` and `val.path` are not properly merged,
            # which may cause SHA3 narrowing errors.
            tx.narrow(solver)  # must do this first if CALLER is hashed
            mutation.path.narrow(solver)
            val.path.narrow(solver)

            if address != LEVEL:
                yield f"To {hex(address)}:\n"

            yield from tx.calldata.describe(solver)
            if solver.evaluate(tx.caller) != PLAYER:
                yield "\tvia proxy"

            yield "\n"
            return

    raise RuntimeError("solution not found")
