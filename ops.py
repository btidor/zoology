"""A library of EVM instruction implementations."""

import copy

from disassembler import Instruction, disassemble
from environment import Contract, Transaction
from smt.bytes import FrozenBytes
from smt.smt import Constraint, Uint8, Uint160, Uint256, Uint257, Uint512
from state import ControlFlow, Descend, Jump, Log, State, Termination


def STOP(s: State) -> None:
    """00 - Halts execution."""
    s.pc = Termination(True, FrozenBytes.concrete())


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
    return (b == Uint256(0)).ite(Uint256(0), a // b)


def SDIV(a: Uint256, b: Uint256) -> Uint256:
    """05 - Signed integer division operation (truncated)."""
    return (b == Uint256(0)).ite(
        Uint256(0), (a.as_signed() // b.as_signed()).as_unsigned()
    )


def MOD(a: Uint256, b: Uint256) -> Uint256:
    """06 - Modulo remainder operation."""
    return (b == Uint256(0)).ite(Uint256(0), a % b)


def SMOD(a: Uint256, b: Uint256) -> Uint256:
    """07 - Signed modulo remainder operation."""
    return (b == Uint256(0)).ite(
        Uint256(0), (a.as_signed() % b.as_signed()).as_unsigned()
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
    exponent = _exponent.unwrap(int, "EXP requires concrete exponent")
    if exponent == 0:
        return Uint256(1)
    for _ in range(exponent - 1):
        a = a * a
    return a


def SIGNEXTEND(b: Uint256, x: Uint256) -> Uint256:
    """0B - Extend length of two's complement signed integer."""
    signoffset = Uint256(8) * b + Uint256(7)
    signbit = (x >> signoffset) & Uint256(0x1)
    mask = ~((Uint256(1) << signoffset) - Uint256(1))
    return Constraint.all(b < Uint256(32), signbit == Uint256(1)).ite(x | mask, x)


def LT(a: Uint256, b: Uint256) -> Uint256:
    """10 - Less-than comparison."""
    return (a < b).ite(Uint256(1), Uint256(0))


def GT(a: Uint256, b: Uint256) -> Uint256:
    """11 - Greater-than comparison."""
    return (a > b).ite(Uint256(1), Uint256(0))


def SLT(a: Uint256, b: Uint256) -> Uint256:
    """12 - Signed less-than comparison."""
    return (a.as_signed() < b.as_signed()).ite(Uint256(1), Uint256(0))


def SGT(a: Uint256, b: Uint256) -> Uint256:
    """13 - Signed greater-than comparison."""
    return (a.as_signed() > b.as_signed()).ite(Uint256(1), Uint256(0))


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
    return (value.as_signed() >> shift).as_unsigned()


def SHA3(s: State, offset: Uint256, size: Uint256) -> Uint256:
    """20 - Compute Keccak-256 hash."""
    return s.sha3[s.memory.slice(offset, size)]


def ADDRESS(s: State) -> Uint256:
    """30 - Get address of currently executing account."""
    return s.contract.address.into(Uint256)


def BALANCE(s: State, address: Uint256) -> Uint256:
    """31 - Get balance of the given account."""
    return s.universe.balances[address.into(Uint160)]


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
    return Uint256.from_bytes(
        *[s.transaction.calldata[i + Uint256(j)] for j in range(32)]
    )


def CALLDATASIZE(s: State) -> Uint256:
    """36 - Get size of input data in current environment."""
    return s.transaction.calldata.length


def CALLDATACOPY(s: State, destOffset: Uint256, offset: Uint256, size: Uint256) -> None:
    """37 - Copy input data in current environment to memory."""
    s.memory.graft(s.transaction.calldata.slice(offset, size), destOffset)


def CODESIZE(s: State) -> Uint256:
    """38 - Get size of code running in current environment."""
    return s.contract.program.code.length


def CODECOPY(s: State, destOffset: Uint256, offset: Uint256, size: Uint256) -> None:
    """39 - Copy code running in current environment to memory."""
    s.memory.graft(s.contract.program.code.slice(offset, size), destOffset)


def GASPRICE(s: State) -> Uint256:
    """3A - Get price of gas in current environment."""
    return s.transaction.gasprice


def EXTCODESIZE(s: State, address: Uint256) -> Uint256:
    """3B - Get size of an account's code."""
    return s.universe.codesizes[address.into(Uint160)]


def EXTCODECOPY(
    s: State,
    _address: Uint256,
    destOffset: Uint256,
    offset: Uint256,
    size: Uint256,
) -> None:
    """3C - Copy an account's code to memory."""
    address = _address.unwrap(int, "EXTCODECOPY requires concrete address")

    contract = s.universe.contracts.get(address, None)
    code = contract.program.code if contract else FrozenBytes.concrete()
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
    address = _address.unwrap(int, "EXTCODEHASH requires concrete address")

    contract = s.universe.contracts.get(address, None)
    if contract is None:
        # TODO: for EOAs we should actually return the empty hash
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
    return s.universe.balances[s.contract.address]


def BASEFEE(s: State) -> Uint256:
    """48 - Get the base fee."""
    return s.block.basefee


def POP(y: Uint256) -> None:
    """50 - Remove item from stack."""
    pass


def MLOAD(s: State, offset: Uint256) -> Uint256:
    """51 - Load word from memory."""
    return Uint256.from_bytes(*[s.memory[offset + Uint256(i)] for i in range(32)])


def MSTORE(s: State, offset: Uint256, value: Uint256) -> None:
    """52 - Save word to memory."""
    for i in range(31, -1, -1):
        s.memory[offset + Uint256(i)] = value.into(Uint8)
        value = value >> Uint256(8)


def MSTORE8(s: State, offset: Uint256, value: Uint256) -> None:
    """53 - Save byte to memory."""
    s.memory[offset] = value.into(Uint8)


def SLOAD(s: State, key: Uint256) -> Uint256:
    """54 - Load word from storage."""
    return s.contract.storage[key]


def SSTORE(s: State, key: Uint256, value: Uint256) -> None:
    """55 - Save word to storage."""
    s.contract.storage[key] = value


def JUMP(s: State, _counter: Uint256) -> None:
    """56 - Alter the program counter."""
    counter = _counter.unwrap(int, "JUMP requires concrete counter")

    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    s.pc = s.contract.program.jumps[counter]


def JUMPI(s: State, _counter: Uint256, b: Uint256) -> ControlFlow | None:
    """57 - Conditionally alter the program counter."""
    counter = _counter.unwrap(int, "JUMPI requires concrete counter")

    s.path <<= 1
    c: Constraint = b == Uint256(0)
    match c.maybe_unwrap():
        case None:  # unknown, must prepare both branches :(
            s0, s1 = copy.deepcopy(s), s
            s0.constraint = Constraint.all(s.constraint, c)

            s1.pc = s.contract.program.jumps[counter]
            s1.path |= 1
            s1.constraint = Constraint.all(s.constraint, ~c)
            return Jump(targets=(s0, s1))
        case True:  # branch never taken, fall through
            return None
        case False:  # branch always taken
            s.pc = s.contract.program.jumps[counter]
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
    initcode = s.memory.slice(offset, size).unwrap(
        "CREATE requires concrete program data"
    )
    sender_address = s.contract.address.unwrap(
        bytes, "CREATE requires concrete sender address"
    )

    # HACK: the destination address depends on the value of this contract's
    # nonce. But we need the destination address to be concrete! So we can only
    # handle CREATE with a concrete state, not a symbolic one. Sorry :(
    nonce = s.contract.nonce.unwrap(int, "CREATE require concrete nonce")
    if nonce >= 0x80:
        raise NotImplementedError  # TODO: implement a full RLP encoder

    # https://ethereum.stackexchange.com/a/761
    seed = FrozenBytes.concrete(b"\xd6\x94" + sender_address + nonce.to_bytes())
    return _CREATE(s, value, initcode, seed)


def _CREATE(
    s: State, value: Uint256, initcode: bytes, seed: FrozenBytes
) -> ControlFlow:
    address = s.sha3[seed].into(Uint160)
    if address.unwrap() in s.universe.contracts:
        raise ValueError(f"CREATE destination exists: 0x{address.unwrap(bytes).hex()}")

    s.contract.nonce += Uint256(1)

    program = disassemble(initcode)
    contract = Contract(address, program)

    # ASSUMPTION: it's possible for a contract to have a non-zero balance upon
    # creation if funds were sent to the address before it was created. Let's
    # ignore this case for now.
    s.universe.balances[address] = Uint256(0)
    s.universe.codesizes[address] = Uint256(0)

    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.contract.address,
        callvalue=value,
        gasprice=s.transaction.gasprice,
    )

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        if substate.pc.success is False:
            state.stack.append(Uint256(0))
        else:
            code = substate.pc.returndata.unwrap()
            program = disassemble(code)

            contract = Contract(address, program, substate.contract.storage)
            state.universe.add_contract(contract)

            state.stack.append(address.into(Uint256))
        return state

    return Descend.new(s, contract, transaction, callback)


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
    codesize = s.universe.codesizes[_address.into(Uint160)]
    if codesize.maybe_unwrap() == 0 or _address.maybe_unwrap() == 0:
        # Simple transfer to an EOA: always succeeds. (We're special-casing the
        # zero address, unfortunately. It has no code and no one controls its
        # keypair.)
        s.transfer(s.contract.address, _address.into(Uint160), value)
        s.latest_return = FrozenBytes.concrete()
        s.memory.graft(s.latest_return.slice(Uint256(0), retSize), retOffset)
        s.stack.append(Uint256(1))
        return None
    elif (address := _address.maybe_unwrap()) is not None:
        # Call to a concrete address: simulate the full execution.
        transaction = Transaction(
            origin=s.transaction.origin,
            caller=s.contract.address,
            callvalue=value,
            calldata=s.memory.slice(argsOffset, argsSize),
            gasprice=s.transaction.gasprice,
        )

        contract = s.universe.contracts.get(address, None)
        if not contract:
            raise ValueError(f"CALL to unknown contract: {hex(address)}")

        def callback(state: State, substate: State) -> State:
            assert isinstance(substate.pc, Termination)
            state.memory.graft(
                substate.pc.returndata.slice(Uint256(0), retSize), retOffset
            )
            state.stack.append(Uint256(1) if substate.pc.success else Uint256(0))
            return state

        return Descend.new(s, contract, transaction, callback)
    else:
        # Call to a symbolic address: return a fully-symbolic response.
        s.latest_return = FrozenBytes.conditional(
            f"RETURNDATA{s.call_count}{s.suffix}",
            s.universe.codesizes[_address.into(Uint160)] == Uint256(0),
        )
        s.memory.graft(s.latest_return.slice(Uint256(0), retSize), retOffset)
        success = Constraint.any(
            # Calls (transfers) to an EOA always succeed.
            (s.universe.codesizes[_address.into(Uint160)] == Uint256(0)),
            # Create a variable for if the call succeeded.
            Constraint(f"RETURNOK{s.call_count}{s.suffix}"),
        )
        s.transfer(s.contract.address, _address.into(Uint160), value)
        s.call_count += 1
        s.stack.append((success).ite(Uint256(1), Uint256(0)))
        return None


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
    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.contract.address,
        callvalue=value,
        calldata=s.memory.slice(argsOffset, argsSize),
        gasprice=s.transaction.gasprice,
    )
    address = _address.unwrap(msg="CALLCODE requires concrete address")
    destination = s.universe.contracts.get(address, None)
    if not destination:
        raise ValueError("CALLCODE to unknown contract: " + hex(address))
    contract = copy.deepcopy(s.contract)
    contract.program = destination.program

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        state.contract.storage = substate.contract.storage
        state.memory.graft(substate.pc.returndata.slice(Uint256(0), retSize), retOffset)
        state.stack.append(Uint256(1) if substate.pc.success else Uint256(0))
        return state

    return Descend.new(s, contract, transaction, callback)


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
) -> ControlFlow:
    """
    F4.

    Message-call into this account with an alternative account's code, but
    persisting the current values for sender and value.
    """
    transaction = Transaction(
        origin=s.transaction.origin,
        caller=s.transaction.caller,
        callvalue=s.transaction.callvalue,
        calldata=s.memory.slice(argsOffset, argsSize),
        gasprice=s.transaction.gasprice,
    )
    address = _address.unwrap(msg="DELEGATECALL requires concrete address")
    destination = s.universe.contracts.get(address, None)
    if not destination:
        raise ValueError("DELEGATECALL to unknown contract: " + hex(address))
    contract = copy.copy(s.contract)
    contract.program = destination.program

    def callback(state: State, substate: State) -> State:
        assert isinstance(substate.pc, Termination)
        state.contract.storage = substate.contract.storage
        state.memory.graft(substate.pc.returndata.slice(Uint256(0), retSize), retOffset)
        state.stack.append(Uint256(1) if substate.pc.success else Uint256(0))
        return state

    return Descend.new(s, contract, transaction, callback)


def CREATE2(
    s: State, value: Uint256, offset: Uint256, size: Uint256, _salt: Uint256
) -> ControlFlow:
    """F5 - Create a new account with associated code at a predictable address."""
    initcode = s.memory.slice(offset, size).unwrap(
        "CREATE2 requires concrete program data"
    )
    salt = _salt.unwrap(bytes, "CREATE2 requires concrete salt")
    sender_address = s.contract.address.unwrap(
        bytes, "CREATE2 requires concrete sender address"
    )
    # https://ethereum.stackexchange.com/a/761
    seed = FrozenBytes.concrete(
        b"\xff"
        + sender_address
        + salt
        + s.sha3[FrozenBytes.concrete(initcode)].unwrap(bytes)
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
    s.pc = Termination(False, FrozenBytes.concrete())


def SELFDESTRUCT() -> None:
    """FF - Halt execution and register account for later deletion."""
    raise NotImplementedError("SELFDESTRUCT")
