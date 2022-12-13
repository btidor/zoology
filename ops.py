"""A library of EVM instruction implementations."""

import z3

from arrays import FrozenBytes
from disassembler import Instruction
from state import State
from symbolic import BW, uint256, unwrap, zand, zconcat, zextract, zif


def STOP(s: State) -> None:
    """00 - Halts execution."""
    s.returndata = FrozenBytes.concrete(b"")
    s.success = True


def ADD(a: uint256, b: uint256) -> uint256:
    """01 - Addition operation."""
    return a + b


def MUL(a: uint256, b: uint256) -> uint256:
    """02 - Multiplication operation."""
    return a * b


def SUB(a: uint256, b: uint256) -> uint256:
    """03 - Subtraction operation."""
    return a - b


def DIV(a: uint256, b: uint256) -> uint256:
    """04 - Integer division operation."""
    return zif(b == 0, BW(0), z3.UDiv(a, b))


def SDIV(a: uint256, b: uint256) -> uint256:
    """05 - Signed integer division operation (truncated)."""
    return zif(b == 0, BW(0), a / b)


def MOD(a: uint256, b: uint256) -> uint256:
    """06 - Modulo remainder operation."""
    return zif(b == 0, BW(0), z3.URem(a, b))


def SMOD(a: uint256, b: uint256) -> uint256:
    """07 - Signed modulo remainder operation."""
    return zif(b == 0, BW(0), a % b)


def ADDMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    """08 - Modulo addition operation."""
    a, b, N = z3.ZeroExt(1, a), z3.ZeroExt(1, b), z3.ZeroExt(1, N)
    return zif(N == 0, BW(0), zextract(255, 0, z3.URem(a + b, N)))


def MULMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    """09 - Modulo multiplication operation."""
    a, b, N = z3.ZeroExt(256, a), z3.ZeroExt(256, b), z3.ZeroExt(256, N)
    return zif(N == 0, BW(0), zextract(255, 0, z3.URem(a * b, N)))


def EXP(a: uint256, _exponent: uint256) -> uint256:
    """0A - Exponential operation."""
    exponent = unwrap(_exponent, "EXP requires concrete exponent")
    if exponent == 0:
        return BW(1)
    for i in range(exponent - 1):
        a = a * a
    return a


def SIGNEXTEND(b: uint256, x: uint256) -> uint256:
    """0B - Extend length of two's complement signed integer."""
    signoffset = 8 * b + 7
    signbit = (x >> signoffset) & 0x1
    mask = ~((1 << signoffset) - 1)
    return zif(zand(z3.ULT(b, 32), signbit == 1), x | mask, x)


def LT(a: uint256, b: uint256) -> uint256:
    """10 - Less-than comparison."""
    return zif(z3.ULT(a, b), BW(1), BW(0))


def GT(a: uint256, b: uint256) -> uint256:
    """11 - Greater-than comparison."""
    return zif(z3.UGT(a, b), BW(1), BW(0))


def SLT(a: uint256, b: uint256) -> uint256:
    """12 - Signed less-than comparison."""
    return zif(a < b, BW(1), BW(0))


def SGT(a: uint256, b: uint256) -> uint256:
    """13 - Signed greater-than comparison."""
    return zif(a > b, BW(1), BW(0))


def EQ(a: uint256, b: uint256) -> uint256:
    """14 - Equality comparison."""
    return zif(a == b, BW(1), BW(0))


def ISZERO(a: uint256) -> uint256:
    """15 - Simple not operator."""
    return zif(a == 0, BW(1), BW(0))


def AND(a: uint256, b: uint256) -> uint256:
    """16 - Bitwise AND operation."""
    return a & b


def OR(a: uint256, b: uint256) -> uint256:
    """17 - Bitwise OR operation."""
    return a | b


def XOR(a: uint256, b: uint256) -> uint256:
    """18 - Bitwise XOR operation."""
    return a ^ b


def NOT(a: uint256) -> uint256:
    """19 - Bitwise NOT operation."""
    return ~a


def BYTE(i: uint256, x: uint256) -> uint256:
    """1A - Retrieve single bytes from word."""
    return zif(
        z3.ULT(i, 32),
        BW(0xFF) & (x >> (8 * (31 - i))),
        BW(0),
    )


def SHL(shift: uint256, value: uint256) -> uint256:
    """1B - Left shift operation."""
    return value << shift


def SHR(shift: uint256, value: uint256) -> uint256:
    """1C - Logical right shift operation."""
    return z3.LShR(value, shift)


def SAR(shift: uint256, value: uint256) -> uint256:
    """1D - Arithmetic (signed) right shift operation."""
    return value >> shift


def SHA3(s: State, offset: uint256, _size: uint256) -> uint256:
    """20 - Compute Keccak-256 hash."""
    size = unwrap(_size, "SHA3 requires concrete size")

    data = zconcat(*[s.memory[offset + BW(i)] for i in range(size)])
    return s.sha3[data]


def ADDRESS(s: State) -> uint256:
    """30 - Get address of currently executing account."""
    return z3.ZeroExt(96, s.contract.address)


def BALANCE(s: State, address: uint256) -> uint256:
    """31 - Get balance of the given account."""
    return s.universe.balances[zextract(159, 0, address)]


def ORIGIN(s: State) -> uint256:
    """32 - Get execution origination address."""
    return z3.ZeroExt(96, s.transaction.origin)


def CALLER(s: State) -> uint256:
    """33 - Get caller address."""
    return z3.ZeroExt(96, s.transaction.caller)


def CALLVALUE(s: State) -> uint256:
    """
    34.

    Get deposited value by the instruction/transaction responsible for this
    execution.
    """
    return s.transaction.callvalue


def CALLDATALOAD(s: State, i: uint256) -> uint256:
    """35 - Get input data of current environment."""
    return zconcat(*[s.transaction.calldata[i + BW(j)] for j in range(32)])


def CALLDATASIZE(s: State) -> uint256:
    """36 - Get size of input data in current environment."""
    return s.transaction.calldata.length


def CALLDATACOPY(s: State, destOffset: uint256, offset: uint256, size: uint256) -> None:
    """37 - Copy input data in current environment to memory."""
    s.memory.splice_from(s.transaction.calldata, destOffset, offset, size)


def CODESIZE(s: State) -> uint256:
    """38 - Get size of code running in current environment."""
    return s.contract.program.code.length


def CODECOPY(s: State, destOffset: uint256, offset: uint256, size: uint256) -> None:
    """39 - Copy code running in current environment to memory."""
    s.memory.splice_from(s.contract.program.code, destOffset, offset, size)


def GASPRICE(s: State) -> uint256:
    """3A - Get price of gas in current environment."""
    return s.transaction.gasprice


def EXTCODESIZE(s: State, _address: uint256) -> uint256:
    """3B - Get size of an account's code."""
    # TODO: support EXTCODESIZE on symbolic addresses, e.g. to check if the
    # caller is an EOA.
    address = unwrap(_address, "EXTCODESIZE requires concrete address")

    contract = s.universe.contracts.get(address, None)
    if contract is None:
        return BW(0)
    return contract.program.code.length


def EXTCODECOPY(
    s: State,
    _address: uint256,
    destOffset: uint256,
    offset: uint256,
    size: uint256,
) -> None:
    """3C - Copy an account's code to memory."""
    address = unwrap(_address, "EXTCODECOPY requires concrete address")

    contract = s.universe.contracts.get(address, None)
    code = contract.program.code if contract else FrozenBytes.concrete(b"")
    s.memory.splice_from(code, destOffset, offset, size)


def RETURNDATASIZE(s: State) -> uint256:
    """
    3D.

    Get size of output data from the previous call from the current environment.
    """
    return s.returndata.length


def RETURNDATACOPY(
    s: State, destOffset: uint256, offset: uint256, size: uint256
) -> None:
    """3E - Copy output data from the previous call to memory."""
    s.memory.splice_from(s.returndata, destOffset, offset, size)


def EXTCODEHASH(s: State, _address: uint256) -> uint256:
    """3F - Get hash of an account's code."""
    address = unwrap(_address, "EXTCODEHASH requires concrete address")

    contract = s.universe.contracts.get(address, None)
    if contract is None:
        # TODO: for EOAs we should actually return the empty hash
        return BW(0)

    return s.sha3[contract.program.code.bigvector()]


def BLOCKHASH(s: State, blockNumber: uint256) -> uint256:
    """40 - Get the hash of one of the 256 most recent complete blocks."""
    return zif(
        z3.ULT(blockNumber, s.block.number - 256),
        BW(0),
        zif(
            z3.UGE(blockNumber, s.block.number),
            BW(0),
            s.universe.blockhashes[blockNumber],
        ),
    )


def COINBASE(s: State) -> uint256:
    """41 - Get the block's beneficiary address."""
    return z3.ZeroExt(96, s.block.coinbase)


def TIMESTAMP(s: State) -> uint256:
    """42 - Get the block's timestamp."""
    return s.block.timestamp


def NUMBER(s: State) -> uint256:
    """43 - Get the block's number."""
    return s.block.number


def PREVRANDAO(s: State) -> uint256:
    """44 - Get the previous block's RANDAO mix."""
    return s.block.prevrandao


def GASLIMIT(s: State) -> uint256:
    """45 - Get the block's gas limit."""
    return s.block.gaslimit


def CHAINID(s: State) -> uint256:
    """46 - Get the chain ID."""
    return s.block.chainid


def SELFBALANCE(s: State) -> uint256:
    """47 - Get balance of currently executing account."""
    return s.universe.balances[s.contract.address]


def BASEFEE(s: State) -> uint256:
    """48 - Get the base fee."""
    return s.block.basefee


def POP(y: uint256) -> None:
    """50 - Remove item from stack."""
    pass


def MLOAD(s: State, offset: uint256) -> uint256:
    """51 - Load word from memory."""
    return zconcat(*[s.memory[offset + BW(i)] for i in range(32)])


def MSTORE(s: State, offset: uint256, value: uint256) -> None:
    """52 - Save word to memory."""
    for i in range(31, -1, -1):
        s.memory[offset + BW(i)] = zextract(7, 0, value)
        value = value >> 8


def MSTORE8(s: State, offset: uint256, value: uint256) -> None:
    """53 - Save byte to memory."""
    s.memory[offset] = zextract(7, 0, value)


def SLOAD(s: State, key: uint256) -> uint256:
    """54 - Load word from storage."""
    return s.contract.storage[key]


def SSTORE(s: State, key: uint256, value: uint256) -> None:
    """55 - Save word to storage."""
    s.contract.storage[key] = value


def JUMP(s: State, _counter: uint256) -> None:
    """56 - Alter the program counter."""
    counter = unwrap(_counter, "JUMP requires concrete counter")
    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    s.pc = s.contract.program.jumps[counter]


def JUMPI(s: State, counter: uint256, b: uint256) -> None:
    """
    57 - Conditionally alter the program counter.

    This opcode should be implemented by the VM, since we may need to fork
    execution.
    """
    raise NotImplementedError("JUMPI")


def PC(ins: Instruction) -> uint256:
    """
    58.

    Get the value of the program counter prior to the increment corresponding to
    this instruction.
    """
    return BW(ins.offset)


def MSIZE(s: State) -> uint256:
    """59 - Get the size of active memory in bytes."""
    return s.memory.length


def GAS(s: State) -> uint256:
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


def PUSH(ins: Instruction) -> uint256:
    """6X/7X - Place N byte item on stack."""
    if ins.operand is None:
        raise ValueError("somehow got a PUSH without an operand")
    return ins.operand


def DUP(ins: Instruction, s: State) -> uint256:
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


def LOG0(offset: uint256, size: uint256) -> None:
    """A0 - Append log record with no topics."""
    # Ignore log records for now, they're mostly for debugging.
    pass


def LOG1(offset: uint256, size: uint256, topic1: uint256) -> None:
    """A1 - Append log record with one topic."""
    pass


def LOG2(offset: uint256, size: uint256, topic1: uint256, topic2: uint256) -> None:
    """A2 - Append log record with two topics."""
    pass


def LOG3(
    offset: uint256, size: uint256, topic1: uint256, topic2: uint256, topic3: uint256
) -> None:
    """A3 - Append log record with three topics."""
    pass


def LOG4(
    offset: uint256,
    size: uint256,
    topic1: uint256,
    topic2: uint256,
    topic3: uint256,
    topic4: uint256,
) -> None:
    """A4 - Append log record with four topics."""
    pass


def CREATE(value: uint256, offset: uint256, size: uint256) -> uint256:
    """F0 - Create a new account with associated code."""
    raise NotImplementedError("CREATE")


def CALL(
    s: State,
    gas: uint256,
    address: uint256,
    value: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    """F1 - Message-call into an account."""
    # TODO: we assume the address is an externally-owned account (i.e. contains
    # no code). How should we handle CALLs to contracts?
    s.returndata = FrozenBytes.concrete(b"")
    s.universe.transfer(s.contract.address, zextract(159, 0, address), value)
    return BW(1)


def CALLCODE(
    gas: uint256,
    address: uint256,
    value: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    """F2 - Message-call into this account with alternative account's code."""
    raise NotImplementedError("CALLCODE")


def RETURN(s: State, offset: uint256, _size: uint256) -> None:
    """F3 - Halts execution returning output data."""
    size = unwrap(_size, "RETURN requires concrete size")
    s.returndata = FrozenBytes.concrete([s.memory[offset + BW(i)] for i in range(size)])
    s.success = True


def DELEGATECALL(
    gas: uint256,
    address: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    """
    F4.

    Message-call into this account with an alternative account's code, but
    persisting the current values for sender and value.

    This opcode should be implemented by the VM.
    """
    raise NotImplementedError("DELEGATECALL")


def CREATE2(value: uint256, offset: uint256, size: uint256, salt: uint256) -> uint256:
    """F5 - Create a new account with associated code at a predictable address."""
    raise NotImplementedError("CREATE2")


def STATICCALL(
    gas: uint256,
    address: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    """FA - Static message-call into an account."""
    raise NotImplementedError("STATICCALL")


def REVERT(s: State, offset: uint256, _size: uint256) -> None:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    size = unwrap(_size, "REVERT requires concrete size")
    s.returndata = FrozenBytes.concrete([s.memory[offset + BW(i)] for i in range(size)])
    s.success = False


def INVALID(s: State) -> None:
    """FE - Designated invalid instruction."""
    s.returndata = FrozenBytes.concrete(b"")
    s.success = False


def SELFDESTRUCT() -> None:
    """FF - Halt execution and register account for later deletion."""
    raise NotImplementedError("SELFDESTRUCT")
