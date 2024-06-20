"""A machine to execute compiled symbolic programs."""

import copy
from typing import Any

from bytes import Bytes
from compiler import compile, symbolic_block, symbolic_transaction
from disassembler import Program, disassemble
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
        (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
    ]

    for term in compile(program):
        k = copy.deepcopy(ki)
        term = term.substitute(subs)

        for i in range(len(term.hyper)):
            hyper = term.hyper[i]
            match hyper:
                case HyperGlobal():
                    k, term = hyperglobal(hyper, k, tx, term)
                case HyperCreate():
                    k, term = hypercreate(hyper, k, tx, term)
                case HyperCall():
                    k, term = hypercall(hyper, k, tx, term)

        assert (ok := term.path.constraint.reveal()) is not None
        if ok:
            if term.storage:
                k.contracts[address].storage = term.storage
            return k, term

    raise RuntimeError("no termination matched")


def hyperglobal(
    h: HyperGlobal[Any, Any], k: Blockchain, _tx: Transaction, term: Terminus
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.input]
    result = h.fn(*input)
    term = term.substitute([(h.result, result)])
    return k, term


def hypercreate(
    h: HyperCreate, k: Blockchain, txi: Transaction, term: Terminus
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete CREATE hypercall."""
    sender = Address.unwrap(txi.address, "CREATE/CREATE2")
    if h.salt is None:
        # https://ethereum.stackexchange.com/a/761
        nonce = k.contracts[sender].nonce
        if nonce >= 0x80:
            raise NotImplementedError  # rlp encoder
        seed = b"\xd6\x94" + sender.to_bytes(20) + nonce.to_bytes(1)
    else:
        salt = h.salt.reveal()
        assert salt is not None, "CREATE2 requires concrete salt"
        digest = term.path.keccak256(h.initcode)
        assert (hash := digest.reveal()) is not None
        seed = b"\xff" + sender.to_bytes(20) + salt.to_bytes(32) + hash.to_bytes(32)
    address = Address.unwrap(term.path.keccak256(Bytes(seed)).into(Uint160))

    tx = Transaction(
        origin=txi.origin,
        caller=txi.address,
        address=Uint160(address),
        callvalue=h.callvalue,
        calldata=Bytes(),
        gasprice=txi.gasprice,
    )
    k.contracts[sender].nonce += 1
    k.contracts[address] = Contract(
        program=disassemble(Bytes()),  # during init, length is zero
    )
    before, after = h.storage
    k.contracts[sender].storage = before
    k.transfer(tx.caller, tx.address, tx.callvalue)

    k, t = execute(k, tx, program=disassemble(h.initcode))
    if t.success:
        k.contracts[address].program = disassemble(t.returndata)
    else:
        del k.contracts[address]

    subs: Substitutions = [
        (h.address, Uint160(address if t.success else 0)),
    ]
    subs.append((after, k.contracts[sender].storage))
    term = term.substitute(subs)
    return k, term


def hypercall(
    h: HyperCall, k: Blockchain, txi: Transaction, term: Terminus
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete CALL, etc. hypercall."""
    sender = Address.unwrap(txi.address, "CALL/DELEGATECALL/STATICCALL")
    address = Address.unwrap(h.address, "CALL/DELEGATECALL/STATICCALL")
    assert (calldata := h.calldata.reveal()) is not None
    tx = Transaction(
        origin=txi.origin,
        caller=txi.caller if h.delegate else txi.address,
        address=txi.address if h.delegate else h.address,
        callvalue=h.callvalue,
        calldata=Bytes(calldata),
        gasprice=txi.gasprice,
    )
    before, after = h.storage
    k.contracts[sender].storage = before
    if not h.delegate:
        k.transfer(tx.caller, tx.address, h.callvalue)

    if address in k.contracts:
        program = k.contracts[address].program if h.delegate else None
        k, t = execute(k, tx, program)
        if h.static:
            assert t.path.static, "STATICCALL executed non-static op"
        assert (returndata := t.returndata.reveal()) is not None
        subs: Substitutions = [
            (h.success, Constraint(t.success)),
            *substitutions(h.returndata, Bytes(returndata)),
        ]
        if after:
            subs.append((after, k.contracts[sender].storage))
    else:
        subs: Substitutions = [
            (h.success, Constraint(True)),
            *substitutions(h.returndata, Bytes()),
        ]
    return k, term.substitute(subs)
