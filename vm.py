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
    substitute,
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
    blockchain: Blockchain,
    address: Address,
    calldata: bytes = b"",
    callvalue: int = 0,
    program: Program | None = None,
) -> tuple[Terminus, Blockchain]:
    """Execute a program with concrete inputs."""
    block, input, value = Block(), Bytes(calldata), Uint256(callvalue)
    transaction = Transaction(
        address=Uint160(address),
        callvalue=value,
        calldata=input,
    )
    if program is None:
        program = blockchain.contracts[address].program
    subs = substitutions(symbolic_block(), block) + substitutions(
        symbolic_transaction(),
        transaction,
    )

    for term in compile(program):
        k = copy.deepcopy(blockchain)
        term = rsubstitute(term, subs)
        extra: Substitutions = [
            (Array[Uint256, Uint256]("STORAGE"), blockchain.contracts[address].storage),
            (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
        ]
        term = rsubstitute(term, extra)
        for i in range(len(term.hyper)):
            hyper = term.hyper[i]
            match hyper:
                case HyperGlobal():
                    k, term = hyperglobal(hyper, k, term)
                case HyperCreate():
                    k, term = hypercreate(hyper, k, term)
                case HyperCall():
                    k, term = hypercall(hyper, k, term, address, program)

        match term.path.constraint.reveal():
            case True:
                return term, k
            case False:
                pass
            case None:
                raise ValueError(
                    f"expected concrete constraint: {term.path.constraint}"
                )

    raise RuntimeError("no termination matched")


def rsubstitute(term: Terminus, subs: Substitutions) -> Terminus:
    """Recursively perform term substitution on the given Terminus."""
    term = substitute(term, subs)
    while extra := term.path.update_substitutions():
        term = substitute(term, extra)
    return term


def hyperglobal(
    h: HyperGlobal[Any, Any], k: Blockchain, term: Terminus
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.input]
    result = h.fn(*input)
    term = rsubstitute(term, [(h.result, result)])
    return k, term


def hypercreate(
    h: HyperCreate, k: Blockchain, term: Terminus
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete CREATE hypercall."""
    sender = Address.unwrap(h.sender, "CREATE/CREATE2")
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
    k.contracts[sender].nonce += 1
    k.contracts[address] = Contract(
        program=disassemble(Bytes()),  # during init, length is zero
    )
    # TODO: customize tx for initcode execution; transfer value

    t, k = execute(k, address, program=disassemble(h.initcode))
    if t.success:
        k.contracts[address].program = disassemble(t.returndata)
    else:
        del k.contracts[address]

    term = rsubstitute(term, [(h.address, Uint160(address if t.success else 0))])
    return k, term


def hypercall(
    h: HyperCall, k: Blockchain, term: Terminus, sender: Address, program: Program
) -> tuple[Blockchain, Terminus]:
    """Simulate a concrete CALL, etc. hypercall."""
    address = Address.unwrap(h.address, "CALL/DELEGATECALL/STATICCALL")
    assert (data := h.calldata.reveal()) is not None
    assert (value := h.callvalue.reveal()) is not None
    override = program if h.delegate else None

    assert (
        k.balances[Uint160(sender)] >= h.callvalue
    ).reveal() is True, "insufficient balance for CALL"
    k.balances[Uint160(sender)] -= h.callvalue
    assert (
        k.balances[Uint160(address)] + h.callvalue >= k.balances[Uint160(address)]
    ).reveal() is True, "CALL overflows destination account"
    k.balances[Uint160(address)] += h.callvalue

    if address in k.contracts:
        t, k = execute(k, address, data, value, override)
        if h.static:
            assert t.path.static
        assert (data := t.returndata.reveal()) is not None
        subs: Substitutions = [(h.success, Constraint(t.success))] + substitutions(
            h.returndata, Bytes(data)
        )
    else:
        subs: Substitutions = [(h.success, Constraint(True))] + substitutions(
            h.returndata, Bytes()
        )
    return k, rsubstitute(term, subs)
