"""A compiler from bytecode to symbolic representation."""

import copy
from heapq import heappop, heappush
from typing import Iterable

from bytes import Bytes
from disassembler import Program
from ops import CreateOp, ForkOp, HyperCreate, TerminateOp, step
from smt import (
    Array,
    Uint8,
    Uint160,
    Uint256,
)
from state import Block, Runtime, Terminus, Transaction


def compile(program: Program) -> Iterable[Terminus]:
    """Compile an EVM contract into a set of symbolic paths."""
    r = Runtime(
        program=program,
        storage=Array[Uint256, Uint256]("STORAGE"),
    )
    block = symbolic_block()
    transaction = symbolic_transaction()

    queue = list[Runtime]([r])
    while queue:
        r = heappop(queue)
        while True:
            match step(r, None, transaction, block):
                case None:
                    pass
                case ForkOp(r0, r1):
                    heappush(queue, r0)
                    heappush(queue, r1)
                    break
                case TerminateOp(success, returndata):
                    storage = r.storage if success and not r.path.static else None
                    yield Terminus(r.path, tuple(r.hyper), success, returndata, storage)
                    break
                case CreateOp() as op:
                    storage = Array[Uint256, Uint256](f"STORAGE{len(r.hyper)}")
                    hyper = HyperCreate(
                        callvalue=op.callvalue,
                        initcode=op.initcode,
                        salt=op.salt,
                        storage=(r.storage, storage),
                        address=Uint160(f"CREATE{len(r.hyper)}"),
                    )
                    r.storage = copy.deepcopy(storage)
                    r.hyper.append(hyper)
                    op.after(r, hyper.address)
                case _:
                    raise NotImplementedError


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
