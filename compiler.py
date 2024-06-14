"""A compiler from bytecode to symbolic representation."""

from heapq import heappop, heappush
from typing import Iterable

from bytes import Bytes
from disassembler import Instruction, Program
from ops import OPS, OpResult
from smt import (
    Array,
    Uint,
    Uint8,
    Uint160,
    Uint256,
)
from state import Block, Runtime, Terminus, Transaction


def compile(program: Program) -> Iterable[Terminus]:
    """Compile an EVM contract into a set of symbolic paths."""
    state = Runtime(
        program=program,
        storage=Array[Uint256, Uint256]("STORAGE"),
    )
    block = symbolic_block()
    transaction = symbolic_transaction()

    queue = list[Runtime]([state])
    while queue:
        state = heappop(queue)
        while True:
            ins = state.program.instructions[state.pc]
            if ins.name not in OPS:
                raise ValueError(f"unimplemented opcode: {ins.name}")

            fn, sig = OPS[ins.name]
            args = list[object]()
            for name in sig.parameters:
                match kls := sig.parameters[name].annotation:
                    case Uint():
                        val = state.stack.pop()
                        args.append(val)
                    case Runtime():
                        args.append(state)
                    case Transaction():
                        args.append(transaction)
                    case Block():
                        args.append(block)
                    case Instruction():
                        args.append(ins)
                    case _:
                        raise TypeError(f"unknown arg class: {kls}")

            # Note: we increment the program counter *before* executing the
            # instruction because instructions may overwrite it (e.g. in the
            # case of a JUMP).
            state.pc += 1

            result: OpResult = fn(*args)
            match result:
                case None:
                    pass
                case Uint():
                    state.stack.append(result)
                    if len(state.stack) > 1024:
                        raise RuntimeError("evm stack overflow")
                case (Runtime(), Runtime()):
                    for state in result:
                        heappush(queue, state)
                    break
                case (success, returndata):
                    storage = (
                        state.storage if success and not state.path.static else None
                    )
                    yield Terminus(state.path, success, returndata, storage)
                    break


# TODO: since they're immutable, these should be global variables, but that
# doesn't seem to work with pytest state resetting.


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
