#!/usr/bin/env python3
"""An implementation of the Ethereum virtual machine."""

import copy
import inspect
from contextlib import contextmanager
from typing import Iterator, List, Literal, Optional, assert_never

import ops
from arrays import Array, FrozenBytes, MutableBytes
from disassembler import Instruction, Program, disassemble
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from smt import Constraint, Uint160, Uint256
from solidity import abiencode, load_solidity
from state import State


def step(
    state: State,
) -> Literal[
    "CONTINUE",
    "JUMPI",
    "GAS",
    "CALL",
    "CALLCODE",
    "DELEGATECALL",
    "STATICCALL",
    "CREATE",
    "TERMINATE",
]:
    """
    Execute a single instruction.

    Mutates state. The caller must handle the return value, which indicates
    whether the program (a) continues normally, or (b) hits a conditional jump
    (JUMPI), or (c) terminates

    In the case of a JUMPI, state is not modified. The caller must evaluate
    whether or not the jump should be taken, update the program counter, and
    optionally add symbolic constraints.
    """
    program = state.contract.program
    ins = program.instructions[state.pc]

    if ins.name == "JUMPI":
        return "JUMPI"
    elif ins.name == "GAS":
        state.pc += 1
        return "GAS"
    elif ins.name == "CALL":
        state.pc += 1
        return "CALL"
    elif ins.name == "CALLCODE":
        state.pc += 1
        return "CALLCODE"
    elif ins.name == "DELEGATECALL":
        state.pc += 1
        return "DELEGATECALL"
    elif ins.name == "STATICCALL":
        state.pc += 1
        return "STATICCALL"
    elif ins.name == "CREATE":
        state.pc += 1
        return "CREATE"
    elif hasattr(ops, ins.name):
        fn = getattr(ops, ins.name)
        sig = inspect.signature(fn)
        args: List[object] = []
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

        result: Optional[Uint256] = fn(*args)
        if result is not None:
            state.stack.append(result)
            if len(state.stack) > 1024:
                raise Exception("evm stack overflow")

        state.pc += 1

        if state.success is None:
            return "CONTINUE"
        else:
            return "TERMINATE"
    else:
        raise ValueError(f"unimplemented opcode: {ins.name}")


def printable_execution(state: State) -> Iterator[str]:
    """
    Invoke a contract with concrete inputs and state.

    Yields a human-readable string at each step of the program.
    """
    program = state.contract.program
    while True:
        # Print next instruction
        ins = program.instructions[state.pc]
        yield str(ins)

        # Execute a single instruction with concrete jumps
        action = step(state)

        if action == "CONTINUE" or action == "TERMINATE":
            pass
        elif action == "JUMPI":
            concrete_JUMPI(state)
        elif action == "GAS":
            concrete_GAS(state)
        elif action == "CALL":
            for substate in hybrid_CALL(state):
                for line in printable_execution(substate):
                    yield "  " + line
        elif action == "CALLCODE":
            with concrete_CALLCODE(state) as substate:
                for line in printable_execution(substate):
                    yield "  " + line
        elif action == "DELEGATECALL":
            with concrete_DELEGATECALL(state) as substate:
                for line in printable_execution(substate):
                    yield "  " + line
        elif action == "STATICCALL":
            with concrete_STATICCALL(state) as substate:
                for line in printable_execution(substate):
                    yield "  " + line
        elif action == "CREATE":
            with concrete_CREATE(state) as substate:
                for line in printable_execution(substate):
                    yield "  " + line
        else:
            assert_never(action)

        # Print stack
        for x in state.stack:
            yield "  " + x.unwrap(bytes).hex()
        yield ""

        if action == "TERMINATE":
            break

    yield ("RETURN" if state.success else "REVERT") + " " + str(
        state.returndata.unwrap()
    )


def concrete_JUMPI(state: State) -> None:
    """Handle a JUMPI action with concrete arguments. Mutates state."""
    program = state.contract.program
    counter = state.stack.pop().unwrap(int, "JUMPI requires concrete counter")
    b = state.stack.pop().unwrap(int, "JUMPI requires concrete b")
    if counter not in program.jumps:
        raise ValueError(f"illegal JUMPI target: 0x{counter:x}")
    if b == 0:
        state.pc += 1
    else:
        state.pc = program.jumps[counter]


def concrete_GAS(state: State) -> None:
    """Handle a GAS action using a concrete dummy value. Mutates state."""
    state.stack.append(Uint256(0x00A500A500A500A500A5))


def hybrid_CALL(state: State) -> Iterator[State]:
    """Handle a CALL action. May yield a single state, or none."""
    gas = state.stack.pop()
    address = state.stack.pop().into(Uint160)
    value = state.stack.pop()
    argsOffset = state.stack.pop()
    argsSize = state.stack.pop()
    retOffset = state.stack.pop()
    retSize = state.stack.pop()

    # TODO: handle calls that mutate storage, including self-calls

    codesize = state.universe.codesizes[address]
    if codesize.maybe_unwrap() == 0:
        # Simple transfer to an EOA: always succeeds.
        state.universe.transfer(state.contract.address, address, value)
        returndata = FrozenBytes.concrete(b"")
        ok = Uint256(1)
    elif (ua := address.maybe_unwrap()) is not None:
        # Call to a concrete address: simulate the full execution.
        transaction = Transaction(
            origin=state.transaction.origin,
            caller=state.contract.address,
            callvalue=value,
            calldata=state.memory.slice(argsOffset, argsSize),
            gasprice=state.transaction.gasprice,
        )

        contract = state.universe.contracts.get(ua, None)
        if not contract:
            raise ValueError(f"CALL to unknown contract: {hex(ua)}")

        with state.descend(contract, transaction) as substate:
            yield substate

            returndata = substate.returndata
            ok = Uint256(1) if substate.success else Uint256(0)
    else:
        # Call to a symbolic address: return a fully-symbolic response.
        returndata = FrozenBytes.conditional(
            f"RETURNDATA{len(state.call_variables)}{state.suffix}",
            state.universe.codesizes[address] == Uint256(0),
        )
        success = Constraint.any(
            # Calls (transfers) to an EOA always succeed.
            (state.universe.codesizes[address] == Uint256(0)),
            # Create a variable for if the call succeeded.
            Constraint(f"RETURNOK{len(state.call_variables)}{state.suffix}"),
        )
        ok = (success).ite(Uint256(1), Uint256(0))
        state.universe.transfer(state.contract.address, address, value)
        state.call_variables.append((state.returndata, success))

    state.returndata = returndata
    state.memory.graft(returndata.slice(Uint256(0), retSize), retOffset)
    state.stack.append(ok)


@contextmanager
def concrete_CALLCODE(state: State) -> Iterator[State]:
    """Handle a CALLCODE action. Yields a single state."""
    gas = state.stack.pop()
    address = state.stack.pop().unwrap(int, "CALLCODE requires concrete address")
    value = state.stack.pop()
    argsOffset = state.stack.pop()
    argsSize = state.stack.pop()
    retOffset = state.stack.pop()
    retSize = state.stack.pop()

    transaction = Transaction(
        origin=state.transaction.origin,
        caller=state.contract.address,
        callvalue=value,
        calldata=state.memory.slice(argsOffset, argsSize),
        gasprice=state.transaction.gasprice,
    )
    other = state.universe.contracts.get(address, None)
    if not other:
        raise ValueError("CALLCODE to unknown contract: " + hex(address))
    contract = copy.copy(state.contract)
    contract.program = other.program

    with state.descend(contract, transaction) as substate:
        yield substate

        state.contract.storage = contract.storage
        state.memory.graft(substate.returndata.slice(Uint256(0), retSize), retOffset)
        state.stack.append(Uint256(1) if substate.success else Uint256(0))


@contextmanager
def concrete_DELEGATECALL(state: State) -> Iterator[State]:
    """Handle a DELEGATECALL action. Yields a single state."""
    gas = state.stack.pop()
    address = state.stack.pop().unwrap(int, "DELEGATECALL requires concrete address")
    argsOffset = state.stack.pop()
    argsSize = state.stack.pop()
    retOffset = state.stack.pop()
    retSize = state.stack.pop()

    transaction = Transaction(
        origin=state.transaction.origin,
        caller=state.transaction.caller,
        callvalue=state.transaction.callvalue,
        calldata=state.memory.slice(argsOffset, argsSize),
        gasprice=state.transaction.gasprice,
    )
    other = state.universe.contracts.get(address, None)
    if not other:
        raise ValueError("DELEGATECALL to unknown contract: " + hex(address))
    contract = copy.copy(state.contract)
    contract.program = other.program

    with state.descend(contract, transaction) as substate:
        yield substate

        state.contract.storage = contract.storage
        state.memory.graft(substate.returndata.slice(Uint256(0), retSize), retOffset)
        state.stack.append(Uint256(1) if substate.success else Uint256(0))


@contextmanager
def concrete_STATICCALL(state: State) -> Iterator[State]:
    """Handle a STATICCALL action. Yields a single state."""
    gas = state.stack.pop()
    address = state.stack.pop().unwrap(int, "STATICCALL requires concrete address")
    argsOffset = state.stack.pop()
    argsSize = state.stack.pop()
    retOffset = state.stack.pop()
    retSize = state.stack.pop()

    raise NotImplementedError("STATICCALL")


@contextmanager
def concrete_CREATE(state: State) -> Iterator[State]:
    """Handle a CREATE action. Yields a single state."""
    value = state.stack.pop()
    offset = state.stack.pop()
    size = state.stack.pop()

    # TODO: this isn't quite right
    init = state.memory.slice(offset, size).unwrap()
    address = Uint160(0x70D070D070D070D070D070D070D070D070D0)
    program = disassemble(init)
    contract = Contract(address, program, Array.concrete(Uint256, Uint256(0)))
    transaction = Transaction(
        origin=state.transaction.origin,
        caller=state.transaction.caller,
        calldata=FrozenBytes.concrete(b""),
        callvalue=value,
        gasprice=state.transaction.gasprice,
    )

    with state.descend(contract, transaction) as substate:
        yield substate

    assert substate.success is not None
    if substate.success is False:
        state.stack.append(Uint256(0))
    else:
        code = substate.returndata.unwrap()
        program = disassemble(code)

        contract = Contract(address, program, substate.contract.storage)
        state.universe.add_contract(contract)

        state.stack.append(address.into(Uint256))


def concrete_start(program: Program, value: Uint256, data: bytes) -> State:
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
    universe.codesizes[contract.address] = contract.program.code.length
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
        returndata=FrozenBytes.concrete(b""),
        success=None,
        subcontexts=[],
        logs=[],
        gas_variables=[],
        call_variables=[],
        path_constraints=[],
        path=1,
    )


if __name__ == "__main__":
    program = load_solidity("fixtures/02_Fallout.sol")
    start = concrete_start(program, Uint256(0), abiencode("collectAllocations()"))

    for line in printable_execution(start):
        print(line)
