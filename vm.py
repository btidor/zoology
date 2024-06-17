"""A machine to execute compiled symbolic programs."""

from typing import Any

from bytes import Bytes
from compiler import compile
from disassembler import Program, disassemble
from smt import (
    Array,
    Constraint,
    Solver,
    Substitutions,
    Uint8,
    Uint64,
    Uint160,
    Uint256,
    substitute,
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
    if program is None:
        program = blockchain.contracts[address].program

    for term in compile(program):
        subs = substitutions(blockchain, address, block, input, value)
        term, k = substitute(term, subs), substitute(blockchain, subs)
        for hyper in term.hyper:
            match hyper:
                case HyperGlobal():
                    k, subs = hyperglobal(hyper, k)
                case HyperCreate():
                    k, subs = hypercreate(hyper, k, term)
                case HyperCall():
                    k, subs = hypercall(hyper, k, program)
            term, k = substitute(term, subs), substitute(k, subs)

        # TODO: make Path produce SHA3 substitutions to keep everything
        # concrete...
        solver = Solver()
        solver.add(term.path.constraint)
        if solver.check():
            term.path.narrow(solver)
            return term, k

    raise RuntimeError("no termination matched")


def substitutions(
    k: Blockchain, address: Address, block: Block, input: Bytes, value: Uint256
) -> Substitutions:
    """Derive variable substitutions for the given state."""
    return [
        # Block
        (Uint256("NUMBER"), block.number),
        (Uint160("COINBASE"), block.coinbase),
        (Uint256("TIMESTAMP"), block.timestamp),
        (Uint256("PREVRANDAO"), block.prevrandao),
        (Uint256("GASLIMIT"), block.gaslimit),
        (Uint256("CHAINID"), block.chainid),
        (Uint256("BASEFEE"), block.basefee),
        (Array[Uint8, Uint256]("BLOCKHASH"), block.hashes),
        # Transaction
        (Uint160("ORIGIN"), Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)),
        (Uint160("CALLER"), Uint160(0xCACACACACACACACACACACACACACACACACACACACA)),
        (Uint160("ADDRESS"), Uint160(address)),
        (Uint256("CALLVALUE"), value),
        (Array[Uint256, Uint8]("CALLDATA"), input.array),
        (Uint64("CALLDATA.length"), input.length.into(Uint64)),
        (Uint256("GASPRICE"), Uint256(0x12)),
        # State
        (Array[Uint256, Uint256]("STORAGE"), k.contracts[address].storage),
        (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
    ]


def hyperglobal(
    h: HyperGlobal[Any, Any], k: Blockchain
) -> tuple[Blockchain, Substitutions]:
    """Simulate a concrete global-state hypercall."""
    input = [k if arg is None else arg for arg in h.input]
    result = h.fn(*input)
    return k, [(h.result, result)]


def hypercreate(
    h: HyperCreate, k: Blockchain, term: Terminus
) -> tuple[Blockchain, Substitutions]:
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

    return k, [(h.address, Uint160(address if t.success else 0))]


def hypercall(
    h: HyperCall, k: Blockchain, program: Program
) -> tuple[Blockchain, Substitutions]:
    """Simulate a concrete CALL, etc. hypercall."""
    address = Address.unwrap(h.address, "CALL/DELEGATECALL/STATICCALL")
    assert (data := h.calldata.reveal()) is not None
    assert (value := h.callvalue.reveal()) is not None
    override = program if h.delegate else None
    t, k = execute(k, address, data, value, override)
    if h.static:
        assert t.path.static
    tmp: Uint64 = t.returndata.length.into(Uint64)
    return k, [
        (h.success, Constraint(t.success)),
        (h.returndata.length.into(Uint64), tmp),
        (h.returndata.array, t.returndata.array),
    ]
