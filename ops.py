from typing import cast

import z3
from Crypto.Hash import keccak

from common import (
    BW,
    BY,
    Block,
    Instruction,
    State,
    require_concrete,
    uint8,
    uint160,
    uint256,
)


# 00 - Halts execution
def STOP(s: State) -> None:
    s.returndata = []
    s.success = True


# 01 - Addition operation
def ADD(a: uint256, b: uint256) -> uint256:
    return a + b


# 02 - Multiplication operation
def MUL(a: uint256, b: uint256) -> uint256:
    return a * b


# 03 - Subtraction operation
def SUB(a: uint256, b: uint256) -> uint256:
    return a - b


# 04 - Integer division operation
def DIV(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(b == 0, BW(0), z3.UDiv(a, b)))


# 05 - Signed integer division operation (truncated)
def SDIV(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(b == 0, BW(0), a / b))


# 06 - Modulo remainder operation
def MOD(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(b == 0, BW(0), z3.URem(a, b)))


# 07 - Signed modulo remainder operation
def SMOD(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(b == 0, BW(0), a % b))


# 08 - Modulo addition operation
def ADDMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    a, b, N = z3.ZeroExt(1, a), z3.ZeroExt(1, b), z3.ZeroExt(1, N)
    return cast(uint256, z3.If(N == 0, BW(0), z3.Extract(255, 0, z3.URem(a + b, N))))


# 09 - Modulo multiplication operation
def MULMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    a, b, N = z3.ZeroExt(256, a), z3.ZeroExt(256, b), z3.ZeroExt(256, N)
    return cast(uint256, z3.If(N == 0, BW(0), z3.Extract(255, 0, z3.URem(a * b, N))))


# 0A - Exponential operation
def EXP(a: uint256, _exponent: uint256) -> uint256:
    exponent = require_concrete(
        _exponent, "EXP(a, exponent) requires concrete exponent"
    )
    if exponent == 0:
        return BW(1)
    for i in range(exponent - 1):
        a = a * a
    return a


# 0B - Extend length of two's complement signed integer
def SIGNEXTEND(_b: uint256, x: uint256) -> uint256:
    b = require_concrete(_b, "SIGNEXTEND(b, x) requires concrete b")
    if b > 30:
        return x
    bits = (b + 1) * 8
    return z3.SignExt(256 - bits, z3.Extract(bits - 1, 0, x))


# 10 - Less-than comparison
def LT(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(z3.ULT(a, b), BW(1), BW(0)))


# 11 - Greater-than comparison
def GT(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(z3.UGT(a, b), BW(1), BW(0)))


# 12 - Signed less-than comparison
def SLT(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(a < b, BW(1), BW(0)))


# 13 - Signed greater-than comparison
def SGT(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(a > b, BW(1), BW(0)))


# 14 - Equality comparison
def EQ(a: uint256, b: uint256) -> uint256:
    return cast(uint256, z3.If(a == b, BW(1), BW(0)))


# 15 - Simple not operator
def ISZERO(a: uint256) -> uint256:
    return cast(uint256, z3.If(a == 0, BW(1), BW(0)))


# 16 - Bitwise AND operation
def AND(a: uint256, b: uint256) -> uint256:
    return a & b


# 17 - Bitwise OR operation
def OR(a: uint256, b: uint256) -> uint256:
    return a | b


# 18 - Bitwise XOR operation
def XOR(a: uint256, b: uint256) -> uint256:
    return a ^ b


# 19 - Bitwise NOT operation
def NOT(a: uint256) -> uint256:
    return ~a


# 1A - Retrieve single bytes from word
def BYTE(_i: uint256, x: uint256) -> uint256:
    i = require_concrete(_i, "BYTE(i, x) requires concrete i")
    if i > 31:
        return BW(0)
    start = 256 - (8 * i)
    return cast(uint256, z3.Extract(start - 1, start - 8, x))


# 1B - Left shift operation
def SHL(shift: uint256, value: uint256) -> uint256:
    return value << shift


# 1C - Logical right shift operation
def SHR(shift: uint256, value: uint256) -> uint256:
    return z3.LShR(value, shift)


# 1D - Arithmetic (signed) right shift operation
def SAR(shift: uint256, value: uint256) -> uint256:
    return value >> shift


# 20 - Compute Keccak-256 hash
def SHA3(s: State, _offset: uint256, _size: uint256) -> uint256:
    offset = require_concrete(_offset, "SHA3(offset, size) requires concrete offset")
    size = require_concrete(_size, "SHA3(offset, size) requires concrete size")

    data = cast(
        z3.BitVecRef,
        z3.simplify(
            z3.Concat(*[s.memory.get(i, BW(0)) for i in range(offset, offset + size)])
        ),
    )

    bits = size * 8
    s.sha3keys.append(data)
    if size not in s.sha3hash:
        s.sha3hash[bits] = z3.Array(
            f"SHA3!{bits}", z3.BitVecSort(bits), z3.BitVecSort(256)
        )

    if z3.is_bv_value(data):
        hash = keccak.new(digest_bits=256)
        hash.update(require_concrete(data).to_bytes(size, "big"))
        s.sha3hash[bits] = cast(
            z3.ArrayRef,
            z3.Store(s.sha3hash[bits], data, BW(int.from_bytes(hash.digest(), "big"))),
        )
    return cast(uint256, s.sha3hash[bits][data])


# 30 - Get address of currently executing account
def ADDRESS(s: State) -> uint256:
    return z3.ZeroExt(96, s.address)


# 31 - Get balance of the given account
def BALANCE(s: State, address: uint256) -> uint256:
    return s.balances[cast(uint160, z3.Extract(159, 0, address))]


# 32 - Get execution origination address
def ORIGIN(s: State) -> uint256:
    return z3.ZeroExt(96, s.origin)


# 33 - Get caller address
def CALLER(s: State) -> uint256:
    return z3.ZeroExt(96, s.caller)


# 34 - Get deposited value by the instruction/transaction responsible for this
# execution
def CALLVALUE(s: State) -> uint256:
    return s.callvalue


# 35 - Get input data of current environment
def CALLDATALOAD(s: State, i: uint256) -> uint256:
    return cast(uint256, z3.Concat(*[s.calldata.get(i + j) for j in range(32)]))


# 36 - Get size of input data in current environment
def CALLDATASIZE(s: State) -> uint256:
    return s.calldata.length()


# 37 - Copy input data in current environment to memory
def CALLDATACOPY(
    s: State, _destOffset: uint256, offset: uint256, _size: uint256
) -> None:
    destOffset = require_concrete(
        _destOffset,
        "CALLDATACOPY(destOffset, offset, size) requires concrete destOffset",
    )
    size = require_concrete(
        _size, "CALLDATACOPY(destOffset, offset, size) requires concrete size"
    )
    for i in range(size):
        s.memory[destOffset + i] = s.calldata.get(offset + i)


# 38 - Get size of code running in current environment
def CODESIZE() -> uint256:
    raise NotImplementedError("CODESIZE")


# 39 - Copy code running in current environment to memory
def CODECOPY(destOffset: uint256, offset: uint256, size: uint256) -> None:
    raise NotImplementedError("CODECOPY")


# 3A - Get price of gas in current environment
def GASPRICE(s: State) -> uint256:
    return s.gasprice


# 3B - Get size of an account's code
def EXTCODESIZE(address: uint256) -> uint256:
    raise NotImplementedError("EXTCODESIZE")


# 3C - Copy an account's code to memory
def EXTCODECOPY(
    address: uint256,
    destOffset: uint256,
    offset: uint256,
    size: uint256,
) -> None:
    raise NotImplementedError("EXTCODECOPY")


# 3D - Get size of output data from the previous call from the current
# environment
def RETURNDATASIZE(s: State) -> uint256:
    return BW(len(s.returndata))


# 3E - Copy output data from the previous call to memory
def RETURNDATACOPY(
    s: State, _destOffset: uint256, _offset: uint256, _size: uint256
) -> None:
    destOffset = require_concrete(
        _destOffset,
        "RETURNDATACOPY(destOffset, offset, size) requires concrete destOffset",
    )
    offset = require_concrete(
        _offset, "RETURNDATACOPY(destOffset, offset, size) requires concrete offset"
    )
    size = require_concrete(
        _size, "RETURNDATACOPY(destOffset, offset, size) requires concrete size"
    )
    for i in range(size):
        s.memory[destOffset + i] = (
            s.returndata[offset + i] if offset + i < len(s.returndata) else BW(0)
        )


# 3F - Get hash of an account's code
def EXTCODEHASH(address: uint256) -> uint256:
    raise NotImplementedError("EXTCODEHASH")


# 40 - Get the hash of one of the 256 most recent complete blocks
def BLOCKHASH(blockNumber: uint256) -> uint256:
    raise NotImplementedError("BLOCKHASH")


# 41 - Get the block's beneficiary address
def COINBASE(b: Block) -> uint256:
    return z3.ZeroExt(96, b.coinbase)


# 42 - Get the block's timestamp
def TIMESTAMP(b: Block) -> uint256:
    return b.timestamp


# 43 - Get the block's number
def NUMBER(b: Block) -> uint256:
    return b.number


# 44 - Get the previous block's RANDAO mix
def PREVRANDAO(b: Block) -> uint256:
    return b.prevrandao


# 45 - Get the block's gas limit
def GASLIMIT(b: Block) -> uint256:
    return b.gaslimit


# 46 - Get the chain ID
def CHAINID(b: Block) -> uint256:
    return b.chainid


# 47 - Get balance of currently executing account
def SELFBALANCE(s: State) -> uint256:
    return s.balances[s.address]


# 48 - Get the base fee
def BASEFEE(b: Block) -> uint256:
    return b.basefee


# 50 - Remove item from stack
def POP(y: uint256) -> None:
    pass


# 51 - Load word from memory
def MLOAD(s: State, _offset: uint256) -> uint256:
    offset = require_concrete(_offset, "MLOAD(offset) requires concrete offset")
    return cast(
        uint256, z3.Concat(*[s.memory.get(offset + i, BY(0)) for i in range(32)])
    )


# 52 - Save word to memory
def MSTORE(s: State, _offset: uint256, value: uint256) -> None:
    offset = require_concrete(_offset, "MSTORE(offset, value) requires concrete offset")
    for i in range(31, -1, -1):
        s.memory[offset + i] = cast(uint8, z3.Extract(7, 0, value))
        value = value >> 8


# 53 - Save byte to memory
def MSTORE8(s: State, _offset: uint256, value: uint8) -> None:
    offset = require_concrete(
        _offset, "MSTORE8(offset, value) requires concrete offset"
    )
    s.memory[offset] = value & 0xFF


# 54 - Load word from storage
def SLOAD(s: State, key: uint256) -> uint256:
    return s.storage[key]


# 55 - Save word to storage
def SSTORE(s: State, key: uint256, value: uint256) -> None:
    s.storage[key] = value


# 56 - Alter the program counter
def JUMP(s: State, _counter: uint256) -> None:
    counter = require_concrete(_counter, "JUMP(counter) requires concrete counter")
    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    s.pc = s.jumps[counter]


# 57 - Conditionally alter the program counter
def JUMPI(s: State, counter: uint256, b: uint256) -> None:
    # This opcode should be implemented by the VM, since we may need to fork
    # execution.
    raise NotImplementedError("JUMPI")


# 58 - Get the value of the program counter prior to the increment corresponding
# to this instruction
def PC(ins: Instruction) -> uint256:
    return BW(ins.offset)


# 59 - Get the size of active memory in bytes
def MSIZE(s: State) -> uint256:
    return BW(max(s.memory.keys()) + 1)


# 5A - Get the amount of available gas, including the corresponding reduction
# for the cost of this instruction)
def GAS() -> uint256:
    raise NotImplementedError("GAS")


# 5B - Marks a valid destination for jumps
def JUMPDEST() -> None:
    pass


# 6X/7X - Place N byte item on stack
def PUSH(ins: Instruction) -> uint256:
    if ins.operand is None:
        raise ValueError("somehow got a PUSH without an operand")
    return ins.operand


# 8X - Duplicate Nth stack item
def DUP(ins: Instruction, s: State) -> uint256:
    if ins.suffix is None:
        raise ValueError("somehow got a DUP without a suffix")
    return s.stack[-ins.suffix]


# 9X - Exchange 1st and (N+1)th stack items
def SWAP(ins: Instruction, s: State) -> None:
    if ins.suffix is None:
        raise ValueError("somehow got a SWAP without a suffix")
    m = ins.suffix + 1
    s.stack[-1], s.stack[-m] = s.stack[-m], s.stack[-1]


# A0 - Append log record with no topics
def LOG0(offset: uint256, size: uint256) -> None:
    # Ignore log records for now, they're mostly for debugging.
    pass


# A1 - Append log record with one topic
def LOG1(offset: uint256, size: uint256, topic1: uint256) -> None:
    pass


# A2 - Append log record with two topics
def LOG2(offset: uint256, size: uint256, topic1: uint256, topic2: uint256) -> None:
    pass


# A3 - Append log record with three topics
def LOG3(
    offset: uint256, size: uint256, topic1: uint256, topic2: uint256, topic3: uint256
) -> None:
    pass


# A4 - Append log record with four topics
def LOG4(
    offset: uint256,
    size: uint256,
    topic1: uint256,
    topic2: uint256,
    topic3: uint256,
    topic4: uint256,
) -> None:
    pass


# F0 - Create a new account with associated code
def CREATE(value: uint256, offset: uint256, size: uint256) -> uint256:
    raise NotImplementedError("CREATE")


# F1 - Message-call into an account
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
    # TODO: we assume the address is an externally-owned account (i.e. contains
    # no code). How should we handle CALLs to contracts?
    s.returndata = []
    s.transfer(cast(uint160, z3.Extract(159, 0, address)), value)
    return BW(1)


# F2 - Message-call into this account with alternative account's code
def CALLCODE(
    gas: uint256,
    address: uint256,
    value: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    raise NotImplementedError("CALLCODE")


# F3 - Halts execution returning output data
def RETURN(s: State, _offset: uint256, _size: uint256) -> None:
    offset = require_concrete(
        _offset,
        "RETURN(offset, size) requires concrete offset",
    )
    size = require_concrete(_size, "RETURN(offset, size) requires concrete size")
    s.returndata = [s.memory.get(i, BW(0)) for i in range(offset, offset + size)]
    s.success = True


# F4 - Message-call into this account with an alternative account’s code, but
# persisting the current values for sender and value
def DELEGATECALL(
    gas: uint256,
    address: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    raise NotImplementedError("DELEGATECALL")


# F5 - Create a new account with associated code at a predictable address
def CREATE2(value: uint256, offset: uint256, size: uint256, salt: uint256) -> uint256:
    raise NotImplementedError("CREATE2")


# FA - Static message-call into an account
def STATICCALL(
    gas: uint256,
    address: uint256,
    argsOffset: uint256,
    argsSize: uint256,
    retOffset: uint256,
    retSize: uint256,
) -> uint256:
    raise NotImplementedError("STATICCALL")


# FD - Halt execution reverting state changes but returning data and remaining
# gas
def REVERT(s: State, _offset: uint256, _size: uint256) -> None:
    offset = require_concrete(
        _offset,
        "REVERT(offset, size) requires concrete offset",
    )
    size = require_concrete(_size, "REVERT(offset, size) requires concrete size")
    s.returndata = [s.memory.get(i, BW(0)) for i in range(offset, offset + size)]
    s.success = False


# FE - Designated invalid instruction
def INVALID(s: State) -> None:
    s.returndata = []
    s.success = False


# FF - Halt execution and register account for later deletion
def SELFDESTRUCT() -> None:
    raise NotImplementedError("SELFDESTRUCT")
