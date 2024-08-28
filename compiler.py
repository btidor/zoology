"""A compiler from bytecode to symbolic representation."""

from heapq import heappop, heappush
from typing import Any, Iterable, cast

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
from state import Block, Blockchain, HyperGlobal, Runtime, Terminus, Transaction


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
            ins = r.program.instructions[r.pc]
            if ins.name not in OPS:
                raise ValueError(f"unimplemented opcode: {ins.name}")

            fn, sig = OPS[ins.name]
            args = list[object]()
            defer = False
            for name in sig.parameters:
                kls = sig.parameters[name].annotation
                if kls == Uint256:
                    val = r.stack.pop()
                    args.append(val)
                elif kls == Runtime:
                    args.append(r)
                elif kls == Transaction:
                    args.append(transaction)
                elif kls == Block:
                    args.append(block)
                elif kls == Instruction:
                    args.append(ins)
                elif kls == Blockchain:
                    args.append(None)
                    defer = True
                else:
                    raise TypeError(f"unknown arg class: {kls}")

            # NOTE: we increment the program counter *before* executing the
            # instruction because instructions may overwrite it (e.g. in the
            # case of a JUMP).
            r.pc += 1

            if defer:
                # NOTE: operations with side effects (i.e. memory writes) cannot
                # be automatically deferred.
                assert not any(isinstance(a, Runtime) for a in args)
                result = Uint256(f"GLOBAL{len(r.hyper)}")
                r.hyper.append(HyperGlobal(cast(Any, args), fn, result))
                r.stack.append(result)
            else:
                result = cast(OpResult, fn(*args))
                match result:
                    case None:
                        pass
                    case Uint():
                        r.stack.append(result)
                        if len(r.stack) > 1024:
                            raise RuntimeError("evm stack overflow")
                    case (Runtime(), Runtime()):
                        for r in result:
                            heappush(queue, r)
                        break
                    case (success, returndata):
                        storage = r.storage if success and not r.path.static else None
                        yield Terminus(
                            r.path, tuple(r.hyper), success, returndata, storage
                        )
                        break


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
