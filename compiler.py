"""A compiler from bytecode to symbolic representation."""

from heapq import heappop, heappush
from typing import Iterable

from disassembler import Instruction, Program
from ops import OPS
from smt import (
    Array,
    Uint,
    Uint160,
    Uint256,
)
from state import State, Termination


def compile(program: Program) -> Iterable[State]:
    """Compile an EVM contract into a set of symbolic paths."""
    state = State(
        program=program,
        storage=Array[Uint256, Uint256]("STORAGE"),
        balance=Array[Uint160, Uint256]("BALANCE"),
    )
    queue = list[State]([state])
    while queue:
        state = heappop(queue)
        while isinstance(state.pc, int):
            ins = state.program.instructions[state.pc]
            if ins.name not in OPS:
                raise ValueError(f"unimplemented opcode: {ins.name}")

            fn, sig = OPS[ins.name]
            args = list[object]()
            for name in sig.parameters:
                kls = sig.parameters[name].annotation
                if kls == Uint256:
                    val = state.stack.pop()
                    args.append(val)
                elif kls == State:
                    args.append(state)
                elif kls == Instruction:
                    args.append(ins)
                else:
                    raise TypeError(f"unknown arg class: {kls}")

            # Note: we increment the program counter *before* executing the
            # instruction because instructions may overwrite it (e.g. in the
            # case of a JUMP).
            state.pc += 1

            result: Uint256 | tuple[State, State] | None = fn(*args)
            match result:
                case None:
                    pass
                case Uint():
                    state.stack.append(result)
                    if len(state.stack) > 1024:
                        raise RuntimeError("evm stack overflow")
                case tuple(states):
                    for state in states:
                        heappush(queue, state)
                    break

        if isinstance(state.pc, Termination):
            yield state
