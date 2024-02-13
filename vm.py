#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

import inspect
from typing import Generator

import ops
from bytes import Bytes
from disassembler import Instruction, Program, abiencode
from environment import Contract, Transaction, Universe
from smt import Uint, Uint160, Uint256
from state import ControlFlow, Descend, Jump, State, Termination


def step(state: State) -> ControlFlow | None:
    """
    Execute a single instruction.

    Mutates state. The caller must handle the return value, which indicates
    whether the program (a) continues normally, (b) hits a conditional jump
    (JUMPI), or (c) terminates.
    """
    assert isinstance(state.pc, int), "program has terminated"

    program = state.contract.program
    ins = program.instructions[state.pc]

    if not hasattr(ops, ins.name):
        raise ValueError(f"unimplemented opcode: {ins.name}")
    fn = getattr(ops, ins.name)

    sig = inspect.signature(fn)
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


def printable_execution(state: State) -> Generator[str, None, State]:
    """
    Invoke a contract with concrete inputs and state.

    Yields a human-readable string at each step of the program.
    """
    program = state.contract.program
    while isinstance(state.pc, int):
        # Print next instruction
        ins = program.instructions[state.pc]
        yield str(ins)

        # Execute a single instruction with concrete jumps
        match step(state):
            case None:
                pass
            case Jump(_):
                raise ValueError("control flow branches on symbolic condition")
            case Descend(substate):
                substate = yield from printable_execution(substate)
                assert substate.recursion is not None
                state = substate.recursion(substate)
            case unknown:
                raise ValueError(f"unknown action: {unknown}")

        # Print stack
        for x in state.stack:
            assert (v := x.reveal()) is not None
            yield "  " + v.to_bytes(32).hex()
        yield ""

    assert isinstance(state.pc, Termination)
    assert (r := state.pc.returndata.reveal()) is not None
    yield ("RETURN" if state.pc.success else "REVERT") + " " + str(r)
    return state


def concrete_start(program: Contract | Program, value: Uint256, data: bytes) -> State:
    """Return a concrete start state with realistic values."""
    contract = program if isinstance(program, Contract) else Contract(program=program)
    transaction = Transaction(
        address=contract.address, callvalue=value, calldata=Bytes(data)
    )
    universe = Universe()
    universe.add_contract(contract)
    universe.codesizes[Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)] = Uint256(0)
    return State(
        contract=contract,
        transaction=transaction,
        universe=universe,
    )


if __name__ == "__main__":
    from tests.solidity import load_solidity

    program = load_solidity("fixtures/02_Fallout.sol")
    start = concrete_start(program, Uint256(0), abiencode("collectAllocations()"))

    for line in printable_execution(start):
        print(line)
