#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

import inspect
from typing import Generator

import ops
from disassembler import Instruction, Program
from environment import Block, Contract, Transaction, Universe
from smt.arrays import Array
from smt.bytes import FrozenBytes, MutableBytes
from smt.sha3 import SHA3
from smt.smt import Uint160, Uint256
from solidity import abiencode, load_solidity
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
    block = Block(
        number=Uint256(16030969),
        coinbase=Uint160(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5),
        timestamp=Uint256(1669214471),
        prevrandao=Uint256(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        ),
        gaslimit=Uint256(30000000000000000),
        chainid=Uint256(1),
        basefee=Uint256(12267131109),
    )
    if isinstance(program, Contract):
        contract = program
    else:
        contract = Contract(
            address=Uint160(0xADADADADADADADADADADADADADADADADADADADAD),
            program=program,
            storage=Array.concrete(Uint256, Uint256(0)),
        )
    transaction = Transaction(
        origin=Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0),
        caller=Uint160(0xCACACACACACACACACACACACACACACACACACACACA),
        callvalue=value,
        calldata=FrozenBytes.concrete(data),
        gasprice=Uint256(0x12),
    )
    universe = Universe(
        suffix="",
        balances=Array.concrete(Uint160, Uint256(0)),
        transfer_constraints=[],
        contracts={},
        codesizes=Array.concrete(Uint160, Uint256(0)),
        blockhashes=Array.concrete(Uint256, Uint256(0)),
        agents=[],
        contribution=Uint256(0),
        extraction=Uint256(0),
    )
    universe.add_contract(contract)
    universe.codesizes[Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)] = Uint256(0)
    return State(
        suffix="",
        block=block,
        contract=contract,
        transaction=transaction,
        universe=universe,
        sha3=SHA3(),
        pc=0,
        stack=[],
        memory=MutableBytes.concrete(b""),
        children=0,
        latest_return=FrozenBytes.concrete(b""),
        logs=[],
        gas_variables=None,
        call_variables=[],
        path_constraints=[],
        path=1,
    )


if __name__ == "__main__":
    program = load_solidity("fixtures/02_Fallout.sol")
    start = concrete_start(program, Uint256(0), abiencode("collectAllocations()"))

    for line in printable_execution(start):
        print(line)
