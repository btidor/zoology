"""A solver for the Ethernaut CTF."""

from __future__ import annotations

from typing import Iterable

from bytes import Bytes
from compiler import (
    Terminus,
    compile,
    symbolic_block,
    symbolic_transaction,
)
from disassembler import abiencode
from smt import Array, Constraint, Solver, Uint8, Uint160, Uint256, substitutions
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import (
    Address,
    Block,
    Blockchain,
    Transaction,
)
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

    k, term = execute(k, tx)
    assert (data := term.returndata.reveal()) is not None
    assert term.success, data

    return k, Address(int.from_bytes(data))


def search(level: int) -> Iterable[str]:
    """Symbolically execute the given level until a solution is found."""
    FACTORY = LEVEL_FACTORIES[level]
    k, LEVEL = load_level(level)

    cblock = Block()
    mblock = cblock.successor()
    vblock = mblock.successor()

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
    subs = [
        *substitutions(symbolic_block(), vblock),
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
        if solver.check(term.path.constraint):
            validators.append(term)
    assert len(validators) == 1
    validator = validators[0]

    for address, contract in k.contracts.items():
        if address == FACTORY:
            continue

        tx = Transaction(
            origin=Uint160(PLAYER),
            caller=Constraint("CALLERAB0").ite(Uint160(PLAYER), Uint160(PROXY)),
            address=Uint160(address),
            callvalue=Uint256("CALLVALUE0"),
            calldata=Bytes.symbolic("CALLDATA0"),
            gasprice=Uint256(0x12),
        )

        for mutation in compile(contract.program):
            if mutation.path.static:  # TODO: or balance change
                continue

            mutation = mutation.substitute(
                [
                    *substitutions(symbolic_transaction(), tx),
                    *substitutions(symbolic_block(), mblock),
                    (
                        Array[Uint256, Uint256]("STORAGE"),
                        k.contracts[address].storage,
                    ),
                ]
            )
            kn, mutation = handle_hypercalls(k, tx, mblock, mutation)
            assert mutation.storage is not None
            kn.contracts[address].storage = mutation.storage

            kn, valn = handle_hypercalls(kn, vx, vblock, validator)
            solver = Solver()
            solver.add(mutation.path.constraint)
            solver.add(valn.path.constraint)
            if not solver.check():
                continue

            tx.narrow(solver)  # must do this first if CALLER is hashed

            # TODO: `mutation.path` and `val.path` are not properly merged,
            # which may cause SHA3 narrowing errors.
            mutation.path.narrow(solver)
            valn.path.narrow(solver)

            if address != LEVEL:
                yield f"To {hex(address)}:\n"

            yield from tx.calldata.describe(solver)
            if solver.evaluate(tx.caller) != PLAYER:
                yield "\tvia proxy"

            yield "\n"
            return

    raise RuntimeError("solution not found")
