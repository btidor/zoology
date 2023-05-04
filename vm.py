#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

import inspect
from typing import Generator

import ops
from disassembler import Instruction, Program, abiencode
from environment import Contract, Transaction, Universe
from smt.bytes import FrozenBytes
from smt.smt import Uint160, Uint256
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
    args: list[object] = []
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
        case Uint256():
            state.stack.append(result)
            if len(state.stack) > 1024:
                raise Exception("evm stack overflow")
            return None
        case ControlFlow():
            # TODO: reduce number of state copies for performance
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
            case Jump(targets):
                matched = [
                    s for (c, s) in targets if c.unwrap("JUMPI requires concrete b")
                ]
                assert len(matched) == 1, "no matching jump target"
                state = matched[0]
            case Descend(substate, callback):
                descent = printable_execution(substate)
                substate = yield from descent
                state = callback(state, substate)
            case unknown:
                raise ValueError(f"unknown action: {unknown}")

        # Print stack
        for x in state.stack:
            yield "  " + x.unwrap(bytes).hex()
        yield ""

    assert isinstance(state.pc, Termination)
    yield ("RETURN" if state.pc.success else "REVERT") + " " + str(
        state.pc.returndata.unwrap()
    )
    return state


def concrete_start(program: Contract | Program, value: Uint256, data: bytes) -> State:
    """Return a concrete start state with realistic values."""
    contract = program if isinstance(program, Contract) else Contract(program=program)
    transaction = Transaction(callvalue=value, calldata=FrozenBytes.concrete(data))
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
