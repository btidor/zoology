"""A library of EVM instruction implementations."""

from arrays import FrozenBytes
from disassembler import Instruction
from smt import Constraint, Uint8, Uint160, Uint256, Uint257, Uint512
from state import State


def STOP(s: State) -> None:
    """00 - Halts execution."""
    s.returndata = FrozenBytes.concrete(b"")
    s.success = True


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
    for i in range(exponent - 1):
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
    """14 -     ity comparison."""
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


def SHA3(s: State, offset: Uint256, _size: Uint256) -> Uint256:
    """20 - Compute Keccak-256 hash."""
    size = _size.unwrap(int, "SHA3 requires concrete size")

    data = FrozenBytes.concrete([s.memory[offset + Uint256(i)] for i in range(size)])
    return s.sha3[data]


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
    code = contract.program.code if contract else FrozenBytes.concrete(b"")
    s.memory.graft(code.slice(offset, size), destOffset)


def RETURNDATASIZE(s: State) -> Uint256:
    """
    3D.

    Get size of output data from the previous call from the current environment.
    """
    return s.returndata.length


def RETURNDATACOPY(
    s: State, destOffset: Uint256, offset: Uint256, size: Uint256
) -> None:
    """3E - Copy output data from the previous call to memory."""
    s.memory.graft(s.returndata.slice(offset, size), destOffset)


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
    return (blockNumber < s.block.number - Uint256(256)).ite(
        Uint256(0),
        (blockNumber >= s.block.number).ite(
            Uint256(0),
            s.universe.blockhashes[blockNumber],
        ),
    )


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
    #
    # Also, set PC to one instruction prior to the JUMPDEST, since the main loop
    # will later increment it.
    s.pc = s.contract.program.jumps[counter] - 1


def JUMPI(s: State, counter: Uint256, b: Uint256) -> None:
    """
    57 - Conditionally alter the program counter.

    This opcode should be implemented by the VM, since we may need to fork
    execution.
    """
    raise NotImplementedError("JUMPI")


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

    This opcode should be implemented by the VM. Since we don't actually track
    gas usage, the VM will need to return either a symbolic value or a concrete
    dummy value.
    """
    raise NotImplementedError("GAS")


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


def LOG0(offset: Uint256, size: Uint256) -> None:
    """A0 - Append log record with no topics."""
    raise NotImplementedError("LOG")


def LOG1(offset: Uint256, size: Uint256, topic1: Uint256) -> None:
    """A1 - Append log record with one topic."""
    raise NotImplementedError("LOG")


def LOG2(offset: Uint256, size: Uint256, topic1: Uint256, topic2: Uint256) -> None:
    """A2 - Append log record with two topics."""
    raise NotImplementedError("LOG")


def LOG3(
    offset: Uint256, size: Uint256, topic1: Uint256, topic2: Uint256, topic3: Uint256
) -> None:
    """A3 - Append log record with three topics."""
    raise NotImplementedError("LOG")


def LOG4(
    offset: Uint256,
    size: Uint256,
    topic1: Uint256,
    topic2: Uint256,
    topic3: Uint256,
    topic4: Uint256,
) -> None:
    """A4 - Append log record with four topics."""
    raise NotImplementedError("LOG")


def CREATE(value: Uint256, offset: Uint256, size: Uint256) -> Uint256:
    """
    F0 - Create a new account with associated code.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("CREATE")


def CALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """
    F1 - Message-call into an account.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("CALL")


def CALLCODE(
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """
    F2 - Message-call into this account with alternative account's code.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("CALLCODE")


def RETURN(s: State, offset: Uint256, size: Uint256) -> None:
    """F3 - Halts execution returning output data."""
    s.returndata = s.memory.slice(offset, size)
    s.success = True


def DELEGATECALL(
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """
    F4.

    Message-call into this account with an alternative account's code, but
    persisting the current values for sender and value.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("DELEGATECALL")


def CREATE2(value: Uint256, offset: Uint256, size: Uint256, salt: Uint256) -> Uint256:
    """F5 - Create a new account with associated code at a predictable address."""
    raise NotImplementedError("CREATE2")


def STATICCALL(
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """
    FA - Static message-call into an account.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("STATICCALL")


def REVERT(s: State, offset: Uint256, size: Uint256) -> None:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    s.returndata = s.memory.slice(offset, size)
    s.success = False


def INVALID(s: State) -> None:
    """FE - Designated invalid instruction."""
    s.returndata = FrozenBytes.concrete(b"")
    s.success = False


def SELFDESTRUCT() -> None:
    """FF - Halt execution and register account for later deletion."""
    raise NotImplementedError("SELFDESTRUCT")
