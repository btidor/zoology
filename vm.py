"""A machine to execute compiled symbolic programs."""

from bytes import Bytes
from compiler import compile
from disassembler import Program, disassemble
from smt import (
    Array,
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
    Hypercall,
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
            term, k = hypercall(k, term, subs, hyper)

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


def hypercall(
    k: Blockchain, term: Terminus, subs: Substitutions, hyper: Hypercall
) -> tuple[Terminus, Blockchain]:
    """Simulate a hypercall."""
    match hyper:
        case HyperGlobal(input, fn, result):
            input = [substitute(arg, subs) if arg else k for arg in input]
            subs = [(result, fn(*input))]
        case HyperCreate(initcode, _value, sender, salt, result):
            sender = Address.unwrap(sender, "CREATE/CREATE2")
            if salt is None:
                # https://ethereum.stackexchange.com/a/761
                nonce = k.contracts[sender].nonce
                if nonce >= 0x80:
                    raise NotImplementedError("rlp encoder")
                seed = b"\xd6\x94" + sender.to_bytes(20) + nonce.to_bytes(1)
            else:
                salt = salt.reveal()
                assert salt is not None, "CREATE2 requires concrete salt"
                digest = term.path.keccak256(initcode)
                assert (h := digest.reveal()) is not None
                seed = (
                    b"\xff" + sender.to_bytes(20) + salt.to_bytes(32) + h.to_bytes(32)
                )

            address = Address.unwrap(term.path.keccak256(Bytes(seed)).into(Uint160))
            k.contracts[sender].nonce += 1
            k.contracts[address] = Contract(
                program=disassemble(Bytes()),  # during init, length is zero
            )
            # TODO: customize tx for initcode execution; transfer value
            t, k = execute(k, address, program=disassemble(initcode))
            if t.success:
                k.contracts[address].program = disassemble(t.returndata)
            else:
                del k.contracts[address]
            subs = [(result, Uint160(address if t.success else 0))]

    return substitute(term, subs), substitute(k, subs)
