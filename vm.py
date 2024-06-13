"""A machine to execute compiled symbolic programs."""

from bytes import Bytes
from smt import Array, Uint8, Uint64, Uint160, Uint256, substitute
from state import Block, State


def execute(
    state: State, block: Block, input: Bytes, storage: Array[Uint256, Uint256]
) -> State:
    """Substitute concrete values in a candidate state transition."""
    return substitute(
        state,
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
            (Uint256("CALLVALUE"), Uint256(0)),
            (Array[Uint256, Uint8]("CALLDATA"), input.array),
            (Uint64("CALLDATA.length"), input.length.into(Uint64)),
            (Uint256("GASPRICE"), Uint256(0x12)),
            # State
            (Array[Uint256, Uint256]("STORAGE"), storage),
            (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
        ],
    )
