"""A machine to execute compiled symbolic programs."""

from bytes import Bytes
from compiler import compile
from smt import Array, Solver, Uint8, Uint64, Uint160, Uint256, substitute
from state import Address, Block, Contracts, Terminus


def execute(
    contracts: Contracts,
    address: Address,
    calldata: bytes = b"",
    callvalue: int = 0,
) -> tuple[Terminus, Contracts]:
    """Execute a program with concrete inputs."""
    block, input, value = Block(), Bytes(calldata), Uint256(callvalue)
    storage = contracts[address].storage

    for term in compile(contracts[address].program):
        term = translate(term, block, input, value, storage)

        solver = Solver()
        solver.add(term.path.constraint)
        if solver.check():
            term.path.narrow(solver)
            return term, contracts

    raise RuntimeError("no termination matched")


def translate(
    term: Terminus,
    block: Block,
    input: Bytes,
    value: Uint256,
    storage: Array[Uint256, Uint256],
) -> Terminus:
    """Substitute concrete values in a candidate state transition."""
    return substitute(
        term,
        [
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
            (Uint160("ADDRESS"), Uint160(0xADADADADADADADADADADADADADADADADADADADAD)),
            (Uint256("CALLVALUE"), value),
            (Array[Uint256, Uint8]("CALLDATA"), input.array),
            (Uint64("CALLDATA.length"), input.length.into(Uint64)),
            (Uint256("GASPRICE"), Uint256(0x12)),
            # State
            (Array[Uint256, Uint256]("STORAGE"), storage),
            (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
        ],
    )
