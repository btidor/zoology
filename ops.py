"""A library of EVM instruction implementations."""

import copy
from typing import Literal

from bytes import Bytes
from disassembler import Instruction, disassemble
from environment import Contract, Transaction
from smt import (
    Array,
    Constraint,
    Int,
    Uint,
    Uint8,
    Uint160,
    Uint256,
    concat_bytes,
)
from state import ControlFlow, DelegateCall, Descend, Jump, Log, State, Termination

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


def EXP(a: Uint256, _exponent: Uint256) -> Uint256:
    """0A - Exponential operation."""
    exponent = _exponent.reveal()
    assert exponent is not None, "EXP requires concrete exponent"

    r = Uint256(1)
    for _ in range(exponent):
        r *= a
    return r


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
    return value >> shift


def SAR(shift: Uint256, value: Uint256) -> Uint256:
    """1D - Arithmetic (signed) right shift operation."""
    return (value.into(Int256) >> shift).into(Uint256)


def KECCAK256(s: State, offset: Uint256, size: Uint256) -> Uint256:
    """20 - Compute Keccak-256 (SHA3) hash."""
    return s.sha3[s.memory.slice(offset, size)]


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
        result = (address == contract.address).ite(contract.program.code.length, result)
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
        # TODO: we should return zero if the address has not been created and
        # the empty hash otherwise.
        return Uint256(0)

    return s.sha3[contract.program.code]


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
    s.storage[key] = value


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
    topics = tuple(s.stack.pop() for _ in range(ins.suffix))
    s.logs.append(Log(s.memory.slice(offset, size), topics))


def CREATE(s: State, value: Uint256, offset: Uint256, size: Uint256) -> ControlFlow:
    """F0 - Create a new account with associated code."""
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
    return _CREATE(s, value, initcode, seed)


def _CREATE(s: State, value: Uint256, initcode: Bytes, seed: Bytes) -> ControlFlow:
    address = s.sha3[seed].into(Uint160)
    assert (destination := address.reveal()) is not None

    sender = s.transaction.address.reveal()
    assert sender is not None, "CREATE requires concrete sender address"
    s.contracts[sender].nonce += Uint256(1)

    constructor = disassemble(initcode)

    # ASSUMPTION: it's possible for a contract to have a non-zero balance upon
    # creation if funds were sent to the address before it was created. Let's
    # ignore this case for now.
    s = s.with_contract(Contract(address=address))
    s.balances[address] = Uint256(0)

    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.transaction.address,
        address=address,
        callvalue=value,
        gasprice=s.transaction.gasprice,
    )

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

    return Descend.new(s, transaction, constructor, callback)


def _callback(
    state: State, substate: State, gas: Uint256, retSize: Uint256, retOffset: Uint256
) -> State:
    assert isinstance(substate.pc, Termination)
    state.memory.graft(state.latest_return.slice(Uint256(0), retSize), retOffset)
    state.stack.append(Constraint(substate.pc.success).ite(Uint256(1), Uint256(0)))
    return state


def CALL(
    s: State,
    gas: Uint256,
    _address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> ControlFlow | None:
    """F1 - Message-call into an account."""
    assert (address := _address.reveal()) is not None, "CALL requires concrete address"
    if address in s.contracts:
        # Call to a contract address: simulate the full execution.
        transaction = Transaction(
            origin=s.transaction.origin,
            caller=s.transaction.address,
            address=_address.into(Uint160),
            callvalue=value,
            calldata=s.memory.slice(argsOffset, argsSize),
            gasprice=s.transaction.gasprice,
        )

        if address not in s.contracts:
            # In theory, calling a nonexistent contract causes it to be created.
            # In practice, this is probably a bug, so we crash the analysis.
            # This means burn addresses need to be explicitly registered, e.g.
            # by setting the codesize to zero.
            raise ValueError(f"CALL to unknown contract: {hex(address)}")

        def callback(state: State, substate: State) -> State:
            return _callback(state, substate, gas, retSize, retOffset)

        return Descend.new(s, transaction, None, callback)
    else:
        # Simple transfer to an EOA: always succeeds.
        s.transfer(s.transaction.address, _address.into(Uint160), value)
        s.latest_return = Bytes()
        s.memory.graft(s.latest_return.slice(Uint256(0), retSize), retOffset)
        s.stack.append(Uint256(1))
        return None

    # TODO: this model is insufficient! We model balances and the return value,
    # but *not* storage changes in the called contract.
    #
    # We should emit cases for all possible targets:
    # - each contract in the universe, including self
    # - proxy that implements $API
    # - proxy that reverts with $MESSAGE
    # - proxy that consumes all gas
    # - player EOA
    # - other, unknown EOA
    # - other, unknown non-EOA (?)
    # - (later: proxy calls a contract in the universe, including self)
    #


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
    address = _address.reveal()
    assert address is not None, "CALLCODE requires concrete address"

    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.transaction.address,
        address=s.transaction.address,
        callvalue=value,
        calldata=s.memory.slice(argsOffset, argsSize),
        gasprice=s.transaction.gasprice,
    )
    destination = s.contracts.get(address, None)
    if destination is None:
        raise ValueError("CALLCODE to unknown contract: " + hex(address))

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        return _callback(state, substate, gas, retSize, retOffset)

    return Descend.new(s, transaction, destination.program, callback)


def RETURN(s: State, offset: Uint256, size: Uint256) -> None:
    """F3 - Halts execution returning output data."""
    s.pc = Termination(True, s.memory.slice(offset, size))


def DELEGATECALL(
    s: State,
    gas: Uint256,
    _address: Uint256,
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
    destination = _address.reveal()
    if destination is None:
        # A DELEGATECALL to an arbitrary contract can overwrite any storage
        # addresses. (Assume we can control the address completely; if not,
        # narrowing will fail.)
        n = len(s.delegates)
        dc = DelegateCall(
            Constraint(f"DCOK{n}{s.suffix}"),
            Bytes.symbolic(f"DCRETURN{n}{s.suffix}"),
            s.storage,
            Array[Uint256, Uint256](f"DCSTORAGE{n}{s.suffix}"),
        )
        # TODO: can we factor out this magic address?
        s.narrower &= _address == Uint256(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
        assert (sender := s.transaction.address.reveal()) is not None
        s.contracts[sender].storage = copy.deepcopy(dc.next_storage)
        s.latest_return = dc.returndata
        s.memory.graft(s.latest_return.slice(Uint256(0), retSize), retOffset)
        s.constraint &= dc.ok | Array.equals(dc.previous_storage, dc.next_storage)
        s.stack.append(dc.ok.ite(Uint256(1), Uint256(0)))
        s.delegates = (*s.delegates, dc)
        return None

    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.transaction.caller,
        address=s.transaction.address,
        callvalue=s.transaction.callvalue,
        calldata=s.memory.slice(argsOffset, argsSize),
        gasprice=s.transaction.gasprice,
    )
    if destination not in s.contracts:
        raise ValueError("DELEGATECALL to unknown contract: " + hex(destination))
    program = s.contracts[destination].program

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        return _callback(state, substate, gas, retSize, retOffset)

    return Descend.new(s, transaction, program, callback)


def CREATE2(
    s: State, value: Uint256, offset: Uint256, size: Uint256, _salt: Uint256
) -> ControlFlow:
    """F5 - Create a new account with associated code at a predictable address."""
    initcode = s.compact_bytes(s.memory.slice(offset, size))
    assert initcode.reveal() is not None, "CREATE2 requires concrete program data"
    # ...because the code is hashed and used in the address, which must be concrete
    salt = _salt.reveal()
    assert salt is not None, "CREATE2 requires concrete salt"
    sender_address = s.transaction.address.reveal()
    assert sender_address is not None, "CREATE2 requires concrete sender address"

    # https://ethereum.stackexchange.com/a/761
    assert (h := s.sha3[initcode].reveal()) is not None
    seed = Bytes(
        b"\xff" + sender_address.to_bytes(20) + salt.to_bytes(32) + h.to_bytes(32)
    )
    return _CREATE(s, value, initcode, seed)


def STATICCALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> ControlFlow | None:
    """FA - Static message-call into an account."""
    # TODO: enforce static constraint
    return CALL(s, gas, address, Uint256(0), argsOffset, argsSize, retOffset, retSize)


def REVERT(s: State, offset: Uint256, size: Uint256) -> None:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    s.pc = Termination(False, s.memory.slice(offset, size))


def INVALID(s: State) -> None:
    """FE - Designated invalid instruction."""
    s.pc = Termination(False, Bytes())


def SELFDESTRUCT() -> None:
    """FF - Halt execution and register account for later deletion."""
    raise NotImplementedError("SELFDESTRUCT")
