#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

from typing import Generator

from bytes import Bytes
from disassembler import Instruction, abiencode
from environment import Transaction
from ops import OPS
from smt import Uint, Uint256
from state import ControlFlow, Descend, Jump, State, Termination, Unreachable
from tests.solidity import load_solidity


def step(state: State) -> ControlFlow | None:
    """
    Execute a single instruction.

    Mutates state. The caller must handle the return value, which indicates
    whether the program (a) continues normally, (b) hits a conditional jump
    (JUMPI), or (c) terminates.
    """
    assert isinstance(state.pc, int), "program has terminated"

    program = state.program
    ins = program.instructions[state.pc]
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

    # Note: we increment the program counter *before* executing the instruction
    # because instructions may overwrite it (e.g. in the case of a JUMP).
    state.pc += 1

    result: Uint256 | ControlFlow | None = fn(*args)
    match result:
        case None:
            return None
        case Uint():
            state.stack.append(result)
            if len(state.stack) > 1024:
                raise Exception("evm stack overflow")
            return None
        case ControlFlow():
            return result


def execute(state: State, /, *, prints: bool = False) -> Generator[str, None, State]:
    """
    Invoke a contract with concrete inputs and state.

    Yields a human-readable string at each step of the program.
    """
    program = state.program
    while isinstance(state.pc, int):
        # Print next instruction
        ins = program.instructions[state.pc]
        if prints:
            yield str(ins)

        # Execute a single instruction with concrete jumps
        match step(state):
            case None:
                pass
            case Jump(_):
                raise ValueError("control flow branches on symbolic condition")
            case Descend(substates):
                if len(substates) > 1:
                    raise ValueError("control flow branches on symbolic condition")
                substate = yield from execute(substates[0], prints=prints)
                if substate.recursion is not None:
                    state = substate.recursion(substate)
            case Unreachable():
                raise ValueError("control flow reached invalid state")
            case unknown:
                raise ValueError(f"unknown action: {unknown}")

        if prints:  # print stack
            for x in state.stack:
                assert (v := x.reveal()) is not None
                yield "  " + v.to_bytes(32).hex()
            yield ""

    assert isinstance(state.pc, Termination)
    if prints:
        assert (r := state.pc.returndata.reveal()) is not None
        yield ("RETURN" if state.pc.success else "REVERT") + " " + str(r)
    return state


if __name__ == "__main__":
    start = State(
        transaction=Transaction(
            callvalue=Uint256(0),
            calldata=Bytes(abiencode("collectAllocations()")),
        ),
    ).with_contract(load_solidity("fixtures/02_Fallout.sol"))

    for line in execute(start, prints=True):
        print(line)
