#!/usr/bin/env python3
"""A compiler from bytecode to symbolic representation."""

from heapq import heappop, heappush
from typing import Iterable

from bytes import Bytes
from disassembler import Instruction, Program, disassemble
from ops import OPS
from smt import (
    Array,
    Solver,
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


def printable_compilation(program: Program) -> Iterable[str]:
    """Produce a human-readable transcript of compilation."""
    for state in compile(program):
        assert isinstance(state.pc, Termination)
        prefix = "*" if not state.static and state.pc.success else "-"
        line = f"{prefix} {state.px().ljust(12)} "

        solver = Solver()
        solver.add(state.constraint)
        if not solver.check():
            yield f"{line}UNREACHABLE"
            continue
        state.narrow(solver)

        calldata = state.transaction.calldata.evaluate(solver).hex()
        prefix, calldata = calldata[:8], calldata[8:]
        line += prefix
        while calldata:
            part, calldata = calldata[:64], calldata[64:]
            line = f"{line} {part}"
        yield line

        line = "  " + ("RETURN" if state.pc.success else "REVERT").ljust(12)
        returndata = state.pc.returndata.evaluate(solver).hex()
        if not state.pc.success:
            prefix, returndata = returndata[:8], returndata[8:]
        else:
            prefix = "        "
        yield f"{line} {prefix} {returndata}"


if __name__ == "__main__":
    code = Bytes.fromhex(
        "608060405234801561001057600080fd5b50600436106100365760003560e01c80631d263f671461003b578063e6f334d714610063575b600080fd5b61004e610049366004610101565b61007a565b60405190151581526020015b60405180910390f35b61006c60005481565b60405190815260200161005a565b600080610088600143610140565b6001549040915081141561009b57600080fd5b60018190556002546000906100b09083610157565b90506000816001146100c35760006100c6565b60015b905084151581151514156100f3576000805490806100e383610179565b9091555060019695505050505050565b505060008080559392505050565b60006020828403121561011357600080fd5b8135801515811461012357600080fd5b9392505050565b634e487b7160e01b600052601160045260246000fd5b6000828210156101525761015261012a565b500390565b60008261017457634e487b7160e01b600052601260045260246000fd5b500490565b600060001982141561018d5761018d61012a565b506001019056fea264697066735822122019b0acf2cc7b361011e29b3b4d16427ec001905ffbf2afb78ffbc731c4e4b5ff64736f6c634300080c0033"
    )
    program = disassemble(code)
    for line in printable_compilation(program):
        print(line)
