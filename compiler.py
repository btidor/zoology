"""A compiler from bytecode to symbolic representation."""

from __future__ import annotations

import copy
from dataclasses import dataclass
from heapq import heappop, heappush
from typing import Any, Iterable, Self

from bytes import Bytes
from disassembler import Program
from environ import Block, Runtime, Transaction
from ops import (
    CallOp,
    CreateOp,
    DeferOp,
    ForkOp,
    TerminateOp,
    step,
)
from path import Path
from smt import (
    Array,
    Constraint,
    Substitutions,
    Uint8,
    Uint160,
    Uint256,
    substitute,
)


def compile(program: Program) -> Iterable[Terminus]:
    """Compile an EVM contract into a set of symbolic paths."""
    r = Runtime(
        program=program,
        storage=Array[Uint256, Uint256]("STORAGE"),
    )
    block = symbolic_block()
    transaction = symbolic_transaction()

    queue = list[tuple[Runtime, list[Hyper]]]([(r, [])])
    while queue:
        r, hyper = heappop(queue)
        while True:
            match step(r, None, transaction, block):
                case None:
                    pass
                case ForkOp(r0, r1):
                    heappush(queue, (r0, hyper))
                    heappush(queue, (r1, copy.copy(hyper)))
                    break
                case TerminateOp(success, returndata):
                    storage = r.storage if success and not r.path.static else None
                    yield Terminus(r.path, tuple(hyper), success, returndata, storage)
                    break
                case CreateOp() | CallOp() as op:
                    if isinstance(op, CreateOp):
                        placeholder = Uint160(f"CREATE{len(hyper)}")
                        op.after(r, placeholder)
                    else:
                        placeholder = (
                            Constraint(f"CALLOK{len(hyper)}"),
                            Bytes.symbolic(f"CALLRET{len(hyper)}"),
                        )
                        op.after(r, *placeholder)
                    storage = Array[Uint256, Uint256](f"STORAGE{len(hyper)}")
                    hyper.append(HyperInvoke(op, (r.storage, storage), placeholder))
                    r.storage = copy.deepcopy(storage)
                case DeferOp() as op:
                    result = Uint256(f"GLOBAL{len(hyper)}")
                    hyper.append(HyperGlobal(op, result))
                    op.after(r, result)


def symbolic_block() -> Block:
    """Return the standard fully-symbolic Block."""
    return Block(
        number=Uint256("NUMBER"),
        coinbase=Uint160("COINBASE"),
        timestamp=Uint256("TIMESTAMP"),
        prevrandao=Uint256("PREVRANDAO"),
        gaslimit=Uint256("GASLIMIT"),
        chainid=Uint256("CHAINID"),
        basefee=Uint256("BASEFEE"),
        hashes=Array[Uint8, Uint256]("BLOCKHASH"),
    )


def symbolic_transaction() -> Transaction:
    """Return the standard fully-symbolic Transaction."""
    return Transaction(
        origin=Uint160("ORIGIN"),
        caller=Uint160("CALLER"),
        address=Uint160("ADDRESS"),
        callvalue=Uint256("CALLVALUE"),
        calldata=Bytes.symbolic("CALLDATA"),
        gasprice=Uint256("GASPRICE"),
    )


@dataclass(frozen=True)
class Terminus:
    """The result of running a contract to completion."""

    path: Path
    hyper: tuple[Hyper, ...]

    success: bool
    returndata: Bytes

    storage: Array[Uint256, Uint256] | None

    def substitute(self, subs: Substitutions) -> Self:
        """
        Perform term substitution.

        If any SHA3 hashes become concrete, term substitution will be
        recursively re-applied until no more hashes can be resolved.
        """
        term = substitute(self, subs)
        while extra := term.path.update_substitutions():
            term = substitute(term, extra)
        return term


@dataclass(frozen=True)
class HyperGlobal:
    """A hypercall for reading information from global state."""

    op: DeferOp
    placeholder: Uint256

    def __deepcopy__(self, memo: Any) -> Self:
        return self


@dataclass(frozen=True)
class HyperInvoke:
    """A hypercall for running code, e.g. via CALL or CREATE."""

    op: CreateOp | CallOp

    storage: tuple[
        Array[Uint256, Uint256],  # before
        Array[Uint256, Uint256],  # after
    ]
    placeholder: Uint160 | tuple[Constraint, Bytes]

    def __deepcopy__(self, memo: Any) -> Self:
        return self


type Hyper = HyperGlobal | HyperInvoke
