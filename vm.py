"""A machine to execute compiled symbolic programs."""

import copy
from typing import Any

from bytes import Bytes
from compiler import compile, symbolic_block, symbolic_transaction
from disassembler import Program, disassemble
from path import Path
from smt import (
    Array,
    Constraint,
    Substitutions,
    Uint160,
    Uint256,
    substitutions,
)
from state import (
    Address,
    Block,
    Blockchain,
    Contract,
    HyperCall,
    HyperCreate,
    HyperGlobal,
    Terminus,
    Transaction,
)


def execute(
    ki: Blockchain, tx: Transaction, program: Program | None = None
) -> tuple[Blockchain, Terminus]:
    """Execute a program with concrete inputs."""
    block, address = Block(), Address.unwrap(tx.address, "execute")
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


def hyperglobal(h: HyperGlobal[Any, Any], k: Blockchain) -> Substitutions:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.input]
    result = h.fn(*input)
    return [(h.result, result)]


def hypercreate(
    h: HyperCreate, k: Blockchain, tx: Transaction, path: Path
) -> tuple[Blockchain, Substitutions, Constraint]:
    """Simulate a concrete CREATE hypercall."""
    sender = Address.unwrap(tx.address, "CREATE/CREATE2")
    if h.salt is None:
        # https://ethereum.stackexchange.com/a/761
        nonce = k.contracts[sender].nonce
        if nonce >= 0x80:
            raise NotImplementedError  # rlp encoder
        seed = b"\xd6\x94" + sender.to_bytes(20) + nonce.to_bytes(1)
    else:
        salt = h.salt.reveal()
        assert salt is not None, "CREATE2 requires concrete salt"
        digest = path.keccak256(h.initcode)
        assert (hash := digest.reveal()) is not None
        seed = b"\xff" + sender.to_bytes(20) + salt.to_bytes(32) + hash.to_bytes(32)
    address = Address.unwrap(path.keccak256(Bytes(seed)).into(Uint160))

    tx = Transaction(
        origin=tx.origin,
        caller=tx.address,
        address=Uint160(address),
        callvalue=h.callvalue,
        calldata=Bytes(),
        gasprice=tx.gasprice,
    )
    k.contracts[sender].nonce += 1
    k.contracts[address] = Contract(
        program=disassemble(Bytes()),  # during init, length is zero
    )
    before, after = h.storage
    k.contracts[sender].storage = before
    ok = k.transfer(tx.caller, tx.address, tx.callvalue)

    k, t = execute(k, tx, program=disassemble(h.initcode))
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
        ok,
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
        k, t = execute(k, tx, program)
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
