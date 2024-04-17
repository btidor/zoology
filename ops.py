"""A library of EVM instruction implementations."""

import copy
from inspect import Signature, signature
from typing import Any, Callable, Literal

from bytes import Bytes
from disassembler import Instruction, Program, disassemble
from environment import Contract, Transaction
from opcodes import REFERENCE, SPECIAL, UNIMPLEMENTED
from smt import (
    Array,
    Constraint,
    Int,
    Uint,
    Uint8,
    Uint64,
    Uint160,
    Uint256,
    bvlshr_harder,
    concat_bytes,
    overflow_safe,
)
from state import (
    Call,
    ControlFlow,
    DelegateCall,
    Descend,
    GasHogCall,
    Jump,
    Log,
    State,
    Termination,
    Unreachable,
)

Int256 = Int[Literal[256]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]


def STOP(s: State) -> None:
    """00 - Halts execution."""
    s.pc = Termination(True, Bytes())


def ADD(a: Uint256, b: Uint256) -> Uint256:
    """01 - Addition operation."""
    return a + b


def MUL(a: Uint256, b: Uint256) -> Uint256:
    """02 - Multiplication operation."""
    return a * b


def SUB(a: Uint256, b: Uint256) -> Uint256:
    """03 - Subtraction operation."""
    return a - b


def DIV(a: Uint256, b: Uint256) -> Uint256:
    """04 - Integer division operation."""
    return (b == Uint256(0)).ite(Uint256(0), a / b)


def SDIV(a: Uint256, b: Uint256) -> Uint256:
    """05 - Signed integer division operation (truncated)."""
    return (b == Uint256(0)).ite(
        Uint256(0), (a.into(Int256) / b.into(Int256)).into(Uint256)
    )


def MOD(a: Uint256, b: Uint256) -> Uint256:
    """06 - Modulo remainder operation."""
    return (b == Uint256(0)).ite(Uint256(0), a % b)


def SMOD(a: Uint256, b: Uint256) -> Uint256:
    """07 - Signed modulo remainder operation."""
    return (b == Uint256(0)).ite(
        Uint256(0), (a.into(Int256) % b.into(Int256)).into(Uint256)
    )


def ADDMOD(a: Uint256, b: Uint256, N: Uint256) -> Uint256:
    """08 - Modulo addition operation."""
    return (N == Uint256(0)).ite(
        Uint256(0),
        ((a.into(Uint257) + b.into(Uint257)) % N.into(Uint257)).into(Uint256),
    )


def MULMOD(a: Uint256, b: Uint256, N: Uint256) -> Uint256:
    """09 - Modulo multiplication operation."""
    return (N == Uint256(0)).ite(
        Uint256(0),
        (a.into(Uint512) * b.into(Uint512) % N.into(Uint512)).into(Uint256),
    )


def EXP(base: Uint256, exponent: Uint256) -> Uint256:
    """0A - Exponential operation."""
    if (exp := exponent.reveal()) is not None:
        # Common case: exponent is concrete, unroll multiplications.
        r = Uint256(1)
        for _ in range(exp):
            r *= base
        return r
    elif (b := base.reveal()) is not None:
        # Fallback: make a table of all possible exponents and results. Assumes
        # base^n (mod 2^256) converges to zero.
        result = Uint256(0)
        concrete = 1
        for i in range(256):
            result = (exponent == Uint256(i)).ite(Uint256(concrete), result)
            concrete = (concrete * b) % (2**256)
            if concrete == 0:
                return result
        raise RecursionError("EXP failed to converge")
    else:
        raise ValueError("EXP requires concrete base or exponent")


def SIGNEXTEND(b: Uint256, x: Uint256) -> Uint256:
    """0B - Extend length of two's complement signed integer."""
    signoffset = Uint256(8) * b + Uint256(7)
    signbit = (x >> signoffset) & Uint256(0x1)
    mask = ~((Uint256(1) << signoffset) - Uint256(1))
    return ((b < Uint256(32)) & (signbit == Uint256(1))).ite(x | mask, x)


def LT(a: Uint256, b: Uint256) -> Uint256:
    """10 - Less-than comparison."""
    return (a < b).ite(Uint256(1), Uint256(0))


def GT(a: Uint256, b: Uint256) -> Uint256:
    """11 - Greater-than comparison."""
    return (a > b).ite(Uint256(1), Uint256(0))


def SLT(a: Uint256, b: Uint256) -> Uint256:
    """12 - Signed less-than comparison."""
    return (a.into(Int256) < b.into(Int256)).ite(Uint256(1), Uint256(0))


def SGT(a: Uint256, b: Uint256) -> Uint256:
    """13 - Signed greater-than comparison."""
    return (a.into(Int256) > b.into(Int256)).ite(Uint256(1), Uint256(0))


def EQ(a: Uint256, b: Uint256) -> Uint256:
    """14 - Equality comparison."""
    return (a == b).ite(Uint256(1), Uint256(0))


def ISZERO(a: Uint256) -> Uint256:
    """15 - Simple not operator."""
    return (a == Uint256(0)).ite(Uint256(1), Uint256(0))


def AND(a: Uint256, b: Uint256) -> Uint256:
    """16 - Bitwise AND operation."""
    return a & b


def OR(a: Uint256, b: Uint256) -> Uint256:
    """17 - Bitwise OR operation."""
    return a | b


def XOR(a: Uint256, b: Uint256) -> Uint256:
    """18 - Bitwise XOR operation."""
    return a ^ b


def NOT(a: Uint256) -> Uint256:
    """19 - Bitwise NOT operation."""
    return ~a


def BYTE(i: Uint256, x: Uint256) -> Uint256:
    """1A - Retrieve single bytes from word."""
    return (i < Uint256(32)).ite(
        Uint256(0xFF) & (x >> (Uint256(8) * (Uint256(31) - i))),
        Uint256(0),
    )


def SHL(shift: Uint256, value: Uint256) -> Uint256:
    """1B - Left shift operation."""
    return value << shift


def SHR(shift: Uint256, value: Uint256) -> Uint256:
    """1C - Logical right shift operation."""
    # Solidity contracts use SHR to extract the function signature from the
    # calldata. It's really important that the result be fully simplified,
    # otherwise we'll waste time exploring irrelevant branches. Bitwuzla doesn't
    # simplify well through `concat`s, so we do it manually.
    return bvlshr_harder(value, shift)


def SAR(shift: Uint256, value: Uint256) -> Uint256:
    """1D - Arithmetic (signed) right shift operation."""
    return (value.into(Int256) >> shift).into(Uint256)


def KECCAK256(s: State, offset: Uint256, size: Uint256) -> Uint256:
    """20 - Compute Keccak-256 (SHA3) hash."""
    digest, constraint = s.sha3.hash(s.memory.slice(offset, size))
    s.constraint &= constraint
    return digest


def ADDRESS(s: State) -> Uint256:
    """30 - Get address of currently executing account."""
    return s.transaction.address.into(Uint256)


def BALANCE(s: State, address: Uint256) -> Uint256:
    """31 - Get balance of the given account."""
    return s.balances[address.into(Uint160)]


def ORIGIN(s: State) -> Uint256:
    """32 - Get execution origination address."""
    return s.transaction.origin.into(Uint256)


def CALLER(s: State) -> Uint256:
    """33 - Get caller address."""
    return s.transaction.caller.into(Uint256)


def CALLVALUE(s: State) -> Uint256:
    """
    34.

    Get deposited value by the instruction/transaction responsible for this
    execution.
    """
    return s.transaction.callvalue


def CALLDATALOAD(s: State, i: Uint256) -> Uint256:
    """35 - Get input data of current environment."""
    return concat_bytes(*[s.transaction.calldata[i + Uint256(j)] for j in range(32)])


def CALLDATASIZE(s: State) -> Uint256:
    """36 - Get size of input data in current environment."""
    return s.transaction.calldata.length


def CALLDATACOPY(s: State, destOffset: Uint256, offset: Uint256, size: Uint256) -> None:
    """37 - Copy input data in current environment to memory."""
    s.memory.graft(s.transaction.calldata.slice(offset, size), destOffset)


def CODESIZE(s: State) -> Uint256:
    """38 - Get size of code running in current environment."""
    return s.program.code.length


def CODECOPY(s: State, destOffset: Uint256, offset: Uint256, size: Uint256) -> None:
    """39 - Copy code running in current environment to memory."""
    s.memory.graft(s.program.code.slice(offset, size), destOffset)


def GASPRICE(s: State) -> Uint256:
    """3A - Get price of gas in current environment."""
    return s.transaction.gasprice


def EXTCODESIZE(s: State, _address: Uint256) -> Uint256:
    """3B - Get size of an account's code."""
    address = _address.into(Uint160)
    result = Uint256(0)
    for contract in s.contracts.values():
        result = (address == contract.address).ite(contract.codesize, result)
    if s.mystery_proxy is not None:
        assert s.mystery_size is not None
        result = (address == s.mystery_proxy).ite(s.mystery_size, result)
    return result


def EXTCODECOPY(
    s: State,
    _address: Uint256,
    destOffset: Uint256,
    offset: Uint256,
    size: Uint256,
) -> None:
    """3C - Copy an account's code to memory."""
    address = _address.reveal()
    assert address is not None, "EXTCODECOPY requires concrete address"

    contract = s.contracts.get(address, None)
    code = contract.program.code if contract else Bytes()
    s.memory.graft(code.slice(offset, size), destOffset)


def RETURNDATASIZE(s: State) -> Uint256:
    """
    3D.

    Get size of output data from the previous call from the current environment.
    """
    return s.latest_return.length


def RETURNDATACOPY(
    s: State, destOffset: Uint256, offset: Uint256, size: Uint256
) -> None:
    """3E - Copy output data from the previous call to memory."""
    s.memory.graft(s.latest_return.slice(offset, size), destOffset)


def EXTCODEHASH(s: State, _address: Uint256) -> Uint256:
    """3F - Get hash of an account's code."""
    address = _address.reveal()
    assert address is not None, "EXTCODEHASH requires concrete address"

    contract = s.contracts.get(address, None)
    if contract is None:
        # Properly, EXTCODEHASH should return zero if the address does not exist
        # or is empty, and the empty hash otherwise. See: EIP-1052.
        raise NotImplementedError("EXTCODEHASH of non-contract address")

    digest, constraint = s.sha3.hash(contract.program.code)
    s.constraint &= constraint
    return digest


def BLOCKHASH(s: State, blockNumber: Uint256) -> Uint256:
    """40 - Get the hash of one of the 256 most recent complete blocks."""
    offset = s.block.number - blockNumber - Uint256(1)
    return (offset < Uint256(256)).ite(s.block.hashes[offset.into(Uint8)], Uint256(0))


def COINBASE(s: State) -> Uint256:
    """41 - Get the block's beneficiary address."""
    return s.block.coinbase.into(Uint256)


def TIMESTAMP(s: State) -> Uint256:
    """42 - Get the block's timestamp."""
    return s.block.timestamp


def NUMBER(s: State) -> Uint256:
    """43 - Get the block's number."""
    return s.block.number


def PREVRANDAO(s: State) -> Uint256:
    """44 - Get the previous block's RANDAO mix."""
    return s.block.prevrandao


def GASLIMIT(s: State) -> Uint256:
    """45 - Get the block's gas limit."""
    return s.block.gaslimit


def CHAINID(s: State) -> Uint256:
    """46 - Get the chain ID."""
    return s.block.chainid


def SELFBALANCE(s: State) -> Uint256:
    """47 - Get balance of currently executing account."""
    return s.balances[s.transaction.address]


def BASEFEE(s: State) -> Uint256:
    """48 - Get the base fee."""
    return s.block.basefee


def POP(y: Uint256) -> None:
    """50 - Remove item from stack."""
    pass


def MLOAD(s: State, offset: Uint256) -> Uint256:
    """51 - Load word from memory."""
    return concat_bytes(*[s.memory[offset + Uint256(i)] for i in range(32)])


def MSTORE(s: State, offset: Uint256, value: Uint256) -> None:
    """52 - Save word to memory."""
    s.memory.setword(offset, value)


def MSTORE8(s: State, offset: Uint256, value: Uint256) -> None:
    """53 - Save byte to memory."""
    s.memory[offset] = value.into(Uint8)


def SLOAD(s: State, key: Uint256) -> Uint256:
    """54 - Load word from storage."""
    return s.storage[key]


def SSTORE(s: State, key: Uint256, value: Uint256) -> None:
    """55 - Save word to storage."""
    if s.changed is None:
        raise ValueError("SSTORE is forbidden during a STATICCALL")
    s.storage[key] = value
    s.changed = True


def JUMP(s: State, _counter: Uint256) -> None:
    """56 - Alter the program counter."""
    counter = _counter.reveal()
    assert counter is not None, "JUMP requires concrete counter"

    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    s.pc = s.program.jumps[counter]


def JUMPI(
    s: State, ins: Instruction, _counter: Uint256, b: Uint256
) -> ControlFlow | None:
    """57 - Conditionally alter the program counter."""
    counter = _counter.reveal()
    assert counter is not None, "JUMPI requires concrete counter"

    s.path <<= 1
    s.cost += 2 ** (s.branching[ins.offset])
    s.branching[ins.offset] += 1
    c = b == Uint256(0)
    match c.reveal():
        case None:  # unknown, must prepare both branches :(
            s0, s1 = copy.deepcopy(s), s
            s0.constraint &= c

            s1.pc = s.program.jumps[counter]
            s1.path |= 1
            s1.constraint &= ~c
            return Jump(targets=(s0, s1))
        case True:  # branch never taken, fall through
            return None
        case False:  # branch always taken
            s.pc = s.program.jumps[counter]
            s.path |= 1
            return None


def PC(ins: Instruction) -> Uint256:
    """
    58.

    Get the value of the program counter prior to the increment corresponding to
    this instruction.
    """
    return Uint256(ins.offset)


def MSIZE(s: State) -> Uint256:
    """59 - Get the size of active memory in bytes."""
    return s.memory.length


def GAS(s: State) -> Uint256:
    """
    5A.

    Get the amount of available gas, including the corresponding reduction for
    the cost of this instruction.

    Since we don't actually track gas usage, return either a symbolic value or a
    concrete dummy value based on the execution mode.
    """
    if s.gas_count is None:
        return Uint256(0x00A500A500A500A500A5)
    else:
        gas = Uint256(f"GAS{s.gas_count}{s.suffix}")
        s.gas_count += 1
        return gas


def JUMPDEST() -> None:
    """5B - Marks a valid destination for jumps."""
    pass


def PUSH(ins: Instruction) -> Uint256:
    """6X/7X - Place N byte item on stack."""
    if ins.operand is None:
        raise ValueError("somehow got a PUSH without an operand")
    return ins.operand


def DUP(ins: Instruction, s: State) -> Uint256:
    """8X - Duplicate Nth stack item."""
    if ins.suffix is None:
        raise ValueError("somehow got a DUP without a suffix")
    return s.stack[-ins.suffix]


def SWAP(ins: Instruction, s: State) -> None:
    """9X - Exchange 1st and (N+1)th stack items."""
    if ins.suffix is None:
        raise ValueError("somehow got a SWAP without a suffix")
    m = ins.suffix + 1
    s.stack[-1], s.stack[-m] = s.stack[-m], s.stack[-1]


def LOG(ins: Instruction, s: State, offset: Uint256, size: Uint256) -> None:
    """AX - Append log record with N topics."""
    if ins.suffix is None:
        raise ValueError("somehow got a LOG without a suffix")
    if s.changed is None:
        raise ValueError(f"LOG{ins.suffix} is forbidden during a STATICCALL")
    topics = tuple(s.stack.pop() for _ in range(ins.suffix))
    s.logs.append(Log(s.memory.slice(offset, size), topics))


def CREATE(s: State, value: Uint256, offset: Uint256, size: Uint256) -> ControlFlow:
    """F0 - Create a new account with associated code."""
    if s.changed is None:
        raise ValueError("CREATE is forbidden during a STATICCALL")
    initcode = s.compact_bytes(s.memory.slice(offset, size))
    sender_address = s.transaction.address.reveal()
    assert sender_address is not None, "CREATE requires concrete sender address"

    # HACK: the destination address depends on the value of this contract's
    # nonce. But we need the destination address to be concrete! So we can only
    # handle CREATE with a concrete state, not a symbolic one. Sorry :(
    nonce = s.contracts[sender_address].nonce.reveal()
    assert nonce is not None, "CREATE require concrete nonce"
    if nonce >= 0x80:
        raise NotImplementedError  # implement a full RLP encoder

    # https://ethereum.stackexchange.com/a/761
    seed = Bytes(b"\xd6\x94" + sender_address.to_bytes(20) + nonce.to_bytes(1))
    return _create_common(s, value, initcode, seed)


def CALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
):
    """F1 - Message-call into an account."""
    return _call_common(
        s,
        gas,
        address,
        value,
        argsOffset,
        argsSize,
        retOffset,
        retSize,
        static=s.changed is None,
        delegate=False,
    )


def CALLCODE(
    s: State,
    gas: Uint256,
    _address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> ControlFlow:
    """F2 - Message-call into this account with alternative account's code."""
    raise NotImplementedError("CALLCODE")


def RETURN(s: State, offset: Uint256, size: Uint256) -> None:
    """F3 - Halts execution returning output data."""
    s.pc = Termination(True, s.memory.slice(offset, size))


def DELEGATECALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> ControlFlow | None:
    """
    F4.

    Message-call into this account with an alternative account's code, but
    persisting the current values for sender and value.
    """
    if s.changed is None:
        raise ValueError("DELEGATECALL is forbidden during a STATICCALL")
    return _call_common(
        s,
        gas,
        address,
        Uint256(0),
        argsOffset,
        argsSize,
        retOffset,
        retSize,
        static=False,
        delegate=True,
    )


def CREATE2(
    s: State, value: Uint256, offset: Uint256, size: Uint256, _salt: Uint256
) -> ControlFlow:
    """F5 - Create a new account with associated code at a predictable address."""
    if s.changed is None:
        raise ValueError("CREATE2 is forbidden during a STATICCALL")
    initcode = s.compact_bytes(s.memory.slice(offset, size))
    assert initcode.reveal() is not None, "CREATE2 requires concrete program data"
    # ...because the code is hashed and used in the address, which must be concrete
    salt = _salt.reveal()
    assert salt is not None, "CREATE2 requires concrete salt"
    sender_address = s.transaction.address.reveal()
    assert sender_address is not None, "CREATE2 requires concrete sender address"

    # https://ethereum.stackexchange.com/a/761
    digest, constraint = s.sha3.hash(initcode)
    s.constraint &= constraint
    assert (h := digest.reveal()) is not None
    seed = Bytes(
        b"\xff" + sender_address.to_bytes(20) + salt.to_bytes(32) + h.to_bytes(32)
    )
    return _create_common(s, value, initcode, seed)


def STATICCALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> ControlFlow:
    """FA - Static message-call into an account."""
    return _call_common(
        s,
        gas,
        address,
        Uint256(0),
        argsOffset,
        argsSize,
        retOffset,
        retSize,
        static=True,
        delegate=False,
    )


def REVERT(s: State, offset: Uint256, size: Uint256) -> None:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    s.pc = Termination(False, s.memory.slice(offset, size))
    s.changed = False


def INVALID(s: State) -> None:
    """FE - Designated invalid instruction."""
    s.pc = Termination(False, Bytes())


def SELFDESTRUCT(s: State, address: Uint256) -> None:
    """FF - Halt execution and register account for later deletion."""
    if s.changed is None:
        raise ValueError("SELFDESTRUCT is forbidden during a STATICCALL")

    contract = s.transaction.address
    recipient = address.into(Uint160)
    value = s.balances[contract]

    # Note: if `current` and `recipient` are equal, the value disappears.
    s.balances[recipient] += value
    s.constraint &= overflow_safe(s.balances[recipient], value)
    s.balances[contract] = Uint256(0)
    s.changed = True

    # HACK: technically this cleanup should be done at the end of the
    # transaction.
    assert (c := contract.reveal()) is not None
    del s.contracts[c]

    s.pc = Termination(True, Bytes())


def _create_common(
    s: State, value: Uint256, initcode: Bytes, seed: Bytes
) -> ControlFlow:
    digest, constraint = s.sha3.hash(seed)
    s.constraint &= constraint
    address = digest.into(Uint160)
    assert (destination := address.reveal()) is not None

    sender = s.transaction.address.reveal()
    assert sender is not None, "CREATE requires concrete sender address"
    s.contracts[sender].nonce += Uint256(1)

    s = s.with_contract(Contract(address=address))
    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.transaction.address,
        address=address,
        callvalue=value,
        gasprice=s.transaction.gasprice,
    )
    constructor = disassemble(initcode)

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        if substate.pc.success is False:
            del state.contracts[destination]
            state.stack.append(Uint256(0))
        else:
            contract = state.contracts[destination]
            contract.program = disassemble(substate.pc.returndata)
            state = state.with_contract(contract, True)
            state.stack.append(address.into(Uint256))
        return state

    return Descend(
        (
            _descend_substate(
                s, transaction, constructor, callback, None, transaction.callvalue
            ),
        )
    )


def _call_common(
    s: State,
    gas: Uint256,
    _address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
    static: bool,
    delegate: bool,
) -> ControlFlow:
    address = _address.into(Uint160)
    calldata = s.memory.slice(argsOffset, argsSize)
    calldata = s.compact_calldata(calldata)
    if calldata is None:
        return Unreachable()

    substates = list[State]()
    eoa = Constraint(True)
    for contract in s.contracts.values():
        if contract.invisible:
            continue
        elif (
            contract.address.reveal() == s.transaction.address.reveal()
            and s.skip_self_calls
        ):
            continue

        cond = address == contract.address
        eoa &= ~cond
        if cond.reveal() is False:
            continue

        s.path <<= 1
        state = copy.deepcopy(s)
        state.path |= 1
        state.constraint &= cond
        if delegate:
            transaction = Transaction(
                origin=state.transaction.origin,
                caller=state.transaction.caller,
                address=state.transaction.address,
                callvalue=state.transaction.callvalue,
                calldata=calldata,
                gasprice=state.transaction.gasprice,
            )
        else:
            transaction = Transaction(
                origin=state.transaction.origin,
                caller=state.transaction.address,
                address=contract.address,
                callvalue=value,
                calldata=calldata,
                gasprice=state.transaction.gasprice,
            )
        # ASSUMPTION: we assume that the CALL does not revert due to running out
        # of gas, attempting to transfer more than the available balance, and
        # other non-modeled conditions.
        substates.append(
            _descend_substate(
                state,
                transaction,
                contract.program if delegate else None,
                (retOffset, retSize),
                gas,
                transaction.callvalue,
                static,
            )
        )

    if s.mystery_proxy is not None:
        cond = address == s.mystery_proxy
        eoa &= ~cond
        if cond.reveal() is not False:
            suffix = f"{s.suffix}-{len(s.calls)}"
            if delegate:
                transaction = Transaction(
                    origin=s.transaction.origin,
                    caller=s.transaction.caller,
                    address=s.transaction.address,
                    callvalue=s.transaction.callvalue,
                    calldata=calldata,
                    gasprice=s.transaction.gasprice,
                )

                # Delegate Case I: proxy reverts, no side effects.
                s.path <<= 1
                state = copy.deepcopy(s)
                state.path |= 1
                state.constraint &= cond
                dc = DelegateCall(
                    transaction,
                    Constraint(False),
                    Bytes.symbolic(f"DCREVERT{suffix}"),
                    (),
                    state.storage,
                    state.storage,
                )
                _apply_call(state, dc, retSize, retOffset)
                substates.append(state)

                # Delegate Case II: proxy overwrites arbitrary storage slot(s)
                # and returns successfully.
                s.path <<= 1
                state = copy.deepcopy(s)
                state.path |= 1
                state.constraint &= cond
                dc = DelegateCall(
                    transaction,
                    Constraint(True),
                    Bytes.symbolic(f"DCRETURN{suffix}"),
                    (),
                    state.storage,
                    Array[Uint256, Uint256](f"DCSTORAGE{suffix}"),
                )
                assert (a := state.transaction.address.reveal()) is not None
                assert dc.next_storage is not None
                state.contracts[a].storage = copy.deepcopy(dc.next_storage)
                _apply_call(state, dc, retSize, retOffset)
                state.changed = True
                substates.append(state)

                # Delegate Case III: proxy invokes SELFDESTRUCT on the contract.
                # For simplicity, assume the value is burned.
                s.path <<= 1
                state = copy.deepcopy(s)
                state.path |= 1
                state.constraint &= cond

                state.balances[state.transaction.address] = Uint256(0)
                state.changed = True

                dc = DelegateCall(
                    transaction,
                    Constraint(True),
                    Bytes(),
                    (),
                    state.storage,
                    None,
                )
                state.calls = (*state.calls, dc)
                state.pc = Termination(True, Bytes())

                # HACK: technically this cleanup should be done at the end of
                # the transaction.
                assert (c := state.transaction.address.reveal()) is not None
                del state.contracts[c]
                substates.append(state)
            else:
                transaction = Transaction(
                    origin=s.transaction.origin,
                    caller=s.transaction.address,
                    address=s.mystery_proxy,
                    callvalue=value,
                    calldata=calldata,
                    gasprice=s.transaction.gasprice,
                )

                # Call Case I: proxy returns or reverts without side effects.
                s.path <<= 1
                state = copy.deepcopy(s)
                state.path |= 1
                state.constraint &= cond
                ok = Constraint(f"RETURNOK{suffix}")
                state.transfer(
                    transaction.caller, transaction.address, ok.ite(value, Uint256(0))
                )
                call = Call(transaction, ok, Bytes.symbolic(f"RETURNDATA{suffix}"), ())
                _apply_call(state, call, retSize, retOffset)
                substates.append(state)

                # Call Case II: proxy consumes all available gas, potentially
                # causing the calling contract to revert.
                s.path <<= 1
                state = copy.deepcopy(s)
                state.path |= 1
                state.cost *= 2
                state.constraint &= cond
                state.gas_hogged += gas
                call = GasHogCall(transaction, Constraint(False), Bytes(), (), gas)
                _apply_call(state, call, retSize, retOffset)
                substates.append(state)

                # Call Case III: proxy makes a reentrant call back into the
                # calling contract, then returns or reverts with a simple value.
                #
                # ASSUMPTION: to prevent infinite loops, we only allow one level
                # of reentrant self-call (and only to the immediate caller).
                #
                # We ignore the possibility of reentrancy during a STATICCALL.
                # Because no writes can occur and no value can be transferred,
                # the proxy can effectively simulate the result of any reentrant
                # call.
                #
                if not static and "R" not in s.suffix and not s.skip_self_calls:
                    s.path <<= 1
                    state = copy.deepcopy(s)
                    state.path |= 1
                    state.constraint &= cond
                    state.transfer(transaction.caller, transaction.address, value)
                    state.suffix += "R"
                    original, state.calls = state.calls, ()
                    reentry = Transaction(
                        origin=s.transaction.origin,
                        caller=s.mystery_proxy,
                        address=s.transaction.address,
                        callvalue=Uint64(f"REENTRYVALUE{state.suffix}").into(Uint256),
                        calldata=Bytes.symbolic(f"REENTRYDATA{state.suffix}"),
                        gasprice=state.transaction.gasprice,
                    )

                    def callback(state: State, substate: State) -> State:
                        assert isinstance(substate.pc, Termination)
                        call = Call(
                            transaction,
                            Constraint(True),
                            Bytes.symbolic(f"RETURNDATA{suffix}"),
                            state.calls,
                        )
                        state.calls = original
                        _apply_call(state, call, retSize, retOffset)
                        if not substate.pc.success:  # skip REVERTs
                            state.constraint = Constraint(False)
                        return state

                    substates.append(
                        _descend_substate(
                            state,
                            reentry,
                            None,
                            callback,
                            gas,
                            reentry.callvalue,
                            static,
                        )
                    )

    if eoa.reveal() is not False:
        s.constraint &= eoa
        if delegate:
            transaction = Transaction(
                origin=s.transaction.origin,
                caller=s.transaction.caller,
                address=s.transaction.address,
                callvalue=s.transaction.callvalue,
                calldata=calldata,
                gasprice=s.transaction.gasprice,
            )
        else:
            transaction = Transaction(
                origin=s.transaction.origin,
                caller=s.transaction.address,
                address=address,
                callvalue=value,
                calldata=calldata,
                gasprice=s.transaction.gasprice,
            )
        s.transfer(transaction.caller, transaction.address, value)
        _apply_call(
            s, Call(transaction, Constraint(True), Bytes(), ()), retSize, retOffset
        )
        substates.append(s)

    return Descend(tuple(substates))


def _apply_call(state: State, call: Call, retSize: Uint256, retOffset: Uint256) -> None:
    state.latest_return = call.returndata
    state.memory.graft(call.returndata.slice(Uint256(0), retSize), retOffset)
    state.stack.append(call.ok.ite(Uint256(1), Uint256(0)))
    state.calls = (*state.calls, call)


def _descend_substate(
    state: State,
    transaction: Transaction,
    program_override: Program | None,
    callback: Callable[[State, State], State] | tuple[Uint256, Uint256],
    gas: Uint256 | None,
    transfer_value: Uint256,
    static: bool = False,
) -> State:
    substate = State(
        suffix=f"{state.suffix}-{len(state.calls)}",
        block=state.block,
        transaction=transaction,
        sha3=state.sha3,
        contracts=copy.deepcopy(state.contracts),
        balances=copy.deepcopy(state.balances),
        program_override=program_override,
        mystery_proxy=state.mystery_proxy,
        mystery_size=state.mystery_size,
        logs=state.logs,
        gas_count=state.gas_count,
        constraint=state.constraint,
        path=state.path,
        cost=state.cost,
        changed=state.changed if not static else None,
        skip_self_calls=state.skip_self_calls,
    )
    substate.transfer(transaction.caller, transaction.address, transfer_value)

    def metacallback(substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        call = Call(
            transaction,
            Constraint(substate.pc.success),
            substate.pc.returndata,
            substate.calls,
        )
        if gas is not None:
            gasok = substate.gas_hogged <= gas
            if gasok.reveal() is not True:
                call = Call(
                    transaction,
                    gasok & call.ok,
                    call.returndata.slice(
                        Uint256(0), gasok.ite(call.returndata.length, Uint256(0))
                    ),
                    substate.calls,
                )
        next = copy.deepcopy(state)
        next.sha3 = substate.sha3
        next.contracts = substate.contracts
        next.balances = substate.balances
        next.mystery_proxy = substate.mystery_proxy
        next.logs = substate.logs
        next.latest_return = call.returndata
        next.gas_count = substate.gas_count
        next.calls = (*next.calls, call)
        next.constraint = substate.constraint
        next.path = substate.path
        next.cost = substate.cost
        if static:
            assert substate.changed is not True
        else:
            next.changed = substate.changed
        assert isinstance(substate.pc, Termination)
        if not substate.pc.success:
            next.contracts = state.contracts
            next.balances = state.balances
            next.changed = state.changed
        match callback:
            case (retOffset, retSize):
                next.memory.graft(call.returndata.slice(Uint256(0), retSize), retOffset)
                next.stack.append(call.ok.ite(Uint256(1), Uint256(0)))
            case _:
                next = callback(next, substate)
        return next

    substate.recursion = metacallback
    return substate


def _load_ops() -> dict[str, tuple[Any, Signature]]:
    opcodes = SPECIAL.union([c.name for c in REFERENCE.values()])
    ops = dict[str, tuple[Any, Signature]]()
    for name in opcodes:
        if name in UNIMPLEMENTED:
            continue
        assert name in globals(), f"unimplemented opcode: {name}"

        fn = globals()[name]
        sig = signature(fn)
        ops[name] = (fn, sig)
    return ops


OPS = _load_ops()
