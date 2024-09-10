"""A solver for the Ethernaut CTF."""

from __future__ import annotations

import copy
from typing import Iterable

from bytes import Bytes
from compiler import (
    Terminus,
    compile,
    symbolic_block,
    symbolic_transaction,
)
from disassembler import abiencode
from environ import (
    Address,
    Block,
    Blockchain,
    Transaction,
)
from smt import (
    Array,
    Constraint,
    Solver,
    Substitutions,
    Uint8,
    Uint160,
    Uint256,
    substitutions,
)
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from vm import execute, handle_hypercalls

PLAYER = 0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0
PROXY = 0xCACACACACACACACACACACACACACACACACACACACA


def load_level(level: int) -> tuple[Blockchain, Address]:
    """Run createInstance() to set up the level."""
    factory = LEVEL_FACTORIES[level]
    k = snapshot_contracts(factory)
    tx = Transaction(
        origin=Uint160(PLAYER),
        caller=Uint160(PLAYER),
        address=Uint160(factory),
        callvalue=Uint256(10**15),
        calldata=Bytes(abiencode("createInstance(address)") + PLAYER.to_bytes(32)),
    )
    k.balances[tx.address] = Uint256(10**15)

    results = list(execute(k, tx))
    assert len(results) == 1
    k, term = results[0]
    assert (data := term.returndata.reveal()) is not None
    assert term.success, data

    return k, Address(int.from_bytes(data))


def search(level: int, depth: int = 10) -> Iterable[str]:
    """Symbolically execute the given level until a solution is found."""
    FACTORY = LEVEL_FACTORIES[level]
    ki, LEVEL = load_level(level)

    block = Block()
    blocks = list[Block]()
    for _ in range(depth):
        block = block.successor()
        blocks.append(block)
    vblock = blocks[-1].successor()

    vx = Transaction(
        origin=Uint160(PLAYER),
        caller=Uint160(PLAYER),
        address=Uint160(FACTORY),
        calldata=Bytes(
            abiencode("validateInstance(address,address)")
            + LEVEL.to_bytes(32)
            + PLAYER.to_bytes(32)
        ),
    )
    vsender = Address.unwrap(vx.address)
    subs: Substitutions = [
        *substitutions(symbolic_block(), vblock),
        *substitutions(symbolic_transaction(), vx),
        (Array[Uint256, Uint256]("STORAGE"), ki.contracts[FACTORY].storage),
    ]

    solver = Solver()
    validators = list[Terminus]()
    for term in compile(ki.contracts[FACTORY].program):
        if not term.success:
            continue
        term = term.substitute(subs)
        term.path.constraint &= term.returndata[Uint256(31)] == Uint8(1)
        if solver.check(term.path.constraint):
            validators.append(term)
    assert len(validators) == 1
    validator = validators[0]

    mutations = list[tuple[Address, Terminus]]()
    for address, contract in ki.contracts.items():
        if address == FACTORY:
            continue

        for mutation in compile(contract.program):
            if not mutation.success:
                continue
            if mutation.path.static:
                # TODO: fix definition of `static` (calls, balance changes)
                continue
            mutations.append((address, mutation))

    paths = list[tuple[Blockchain, list[tuple[Address, Transaction, Terminus]]]]()
    paths.append((ki, []))
    for i in range(depth):
        next = list[tuple[Blockchain, list[tuple[Address, Transaction, Terminus]]]]()
        for kj, hj in paths:
            for address, mutation in mutations:
                tx = Transaction(
                    origin=Uint160(PLAYER),
                    caller=Constraint(f"CALLERAB{i}").ite(
                        Uint160(PLAYER), Uint160(PROXY)
                    ),
                    address=Uint160(address),
                    callvalue=Uint256(f"CALLVALUE{i}"),
                    calldata=Bytes.symbolic(f"CALLDATA{i}"),
                    gasprice=Uint256(0x12),
                )
                k, mutation = copy.deepcopy((kj, mutation))
                mutation = mutation.substitute(
                    [
                        *substitutions(symbolic_transaction(), tx),
                        *substitutions(symbolic_block(), blocks[i]),
                        (
                            Array[Uint256, Uint256]("STORAGE"),
                            k.contracts[address].storage,
                        ),
                    ]
                )
                if mutation.path.constraint.reveal() is False:
                    continue

                for k, mutation in handle_hypercalls(
                    k, tx, address, blocks[i], mutation
                ):
                    assert mutation.storage is not None
                    k.contracts[address].storage = mutation.storage

                    history = hj + [(address, tx, mutation)]
                    next.append((copy.deepcopy(k), history))

                    result = _validate(k, vx, vsender, vblock, validator, history)
                    if result is None:
                        continue
                    valn, solver = result

                    for _, tx, _ in history:
                        tx.narrow(solver)  # must do this first if CALLER is hashed

                    # TODO: `mutation.path` and `val.path` are not properly
                    # merged, which may cause SHA3 narrowing errors.
                    for _, _, mutation in history:
                        mutation.path.narrow(solver)
                    valn.path.narrow(solver)

                    for address, tx, _ in history:
                        if address != LEVEL:
                            yield f"To {hex(address)}:\n"
                        yield from tx.calldata.describe(solver)
                        if solver.evaluate(tx.caller) != PLAYER:
                            yield "\tvia proxy"
                        yield "\n"
                    return

        paths = next

    raise RuntimeError("solution not found")


def _validate(
    k: Blockchain,
    tx: Transaction,
    sender: Address,
    block: Block,
    term: Terminus,
    history: list[tuple[Address, Transaction, Terminus]],
) -> tuple[Terminus, Solver] | None:
    for k, term in handle_hypercalls(k, tx, sender, block, term):
        solver = Solver()
        for _, _, mutation in history:
            solver.add(mutation.path.constraint)
        solver.add(term.path.constraint)
        if not solver.check():
            continue
        return term, solver
    return None
