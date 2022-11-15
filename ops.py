from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import cast

import z3
from Crypto.Hash import keccak

from common import BW, BY, Address, State, uint8, uint256


def require_concrete(var: uint256, msg: str) -> int:
    var = z3.simplify(var)
    if not z3.is_bv_value(var):
        raise ValueError(msg)
    return cast(int, var.as_long())


@dataclass
class Block:
    number: uint256 = 0
    coinbase: Address = 0
    timestamp: uint256 = 0
    prevrandao: uint256 = 0
    gaslimit: uint256 = 0
    chainid: uint256 = 1
    basefee: uint256 = 0


class World(ABC):
    @abstractmethod
    def balance(self, address: Address) -> uint256:
        pass

    @abstractmethod
    def code(self, address: Address) -> bytes:
        pass

    @abstractmethod
    def blockhash(self, blockNumber: int) -> int:
        pass


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
    return z3.If(b == 0, BW(0), z3.UDiv(a, b))


# 05 - Signed integer division operation (truncated)
def SDIV(a: uint256, b: uint256) -> uint256:
    return z3.If(b == 0, BW(0), a / b)


# 06 - Modulo remainder operation
def MOD(a: uint256, b: uint256) -> uint256:
    return z3.If(b == 0, BW(0), z3.URem(a, b))


# 07 - Signed modulo remainder operation
def SMOD(a: uint256, b: uint256) -> uint256:
    return z3.If(b == 0, BW(0), a % b)


# 08 - Modulo addition operation
def ADDMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    a, b, N = z3.ZeroExt(1, a), z3.ZeroExt(1, b), z3.ZeroExt(1, N)
    return z3.If(N == 0, BW(0), z3.Extract(255, 0, z3.URem(a + b, N)))


# 09 - Modulo multiplication operation
def MULMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    a, b, N = z3.ZeroExt(256, a), z3.ZeroExt(256, b), z3.ZeroExt(256, N)
    return z3.If(N == 0, BW(0), z3.Extract(255, 0, z3.URem(a * b, N)))


# 0A - Exponential operation
def EXP(a: uint256, exponent: uint256) -> uint256:
    exponent = require_concrete(exponent, "EXP(a, exponent) requires concrete exponent")
    if exponent == 0:
        return BW(1)
    for i in range(exponent - 1):
        a = a * a
    return a


# 0B - Extend length of two's complement signed integer
def SIGNEXTEND(b: uint256, x: uint256) -> uint256:
    b = require_concrete(b, "SIGNEXTEND(b, x) requires concrete b")
    if b > 30:
        return x
    bits = (b + 1) * 8
    return z3.SignExt(256 - bits, z3.Extract(bits - 1, 0, x))


# 10 - Less-than comparison
def LT(a: uint256, b: uint256) -> uint256:
    return z3.If(z3.ULT(a, b), BW(1), BW(0))


# 11 - Greater-than comparison
def GT(a: uint256, b: uint256) -> uint256:
    return z3.If(z3.UGT(a, b), BW(1), BW(0))


# 12 - Signed less-than comparison
def SLT(a: uint256, b: uint256) -> uint256:
    return z3.If(a < b, BW(1), BW(0))


# 13 - Signed greater-than comparison
def SGT(a: uint256, b: uint256) -> uint256:
    return z3.If(a > b, BW(1), BW(0))


# 14 - Equality comparison
def EQ(a: uint256, b: uint256) -> uint256:
    return z3.If(a == b, BW(1), BW(0))


# 15 - Simple not operator
def ISZERO(a: uint256) -> uint256:
    return z3.If(a == 0, BW(1), BW(0))


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
def BYTE(i: uint256, x: uint256) -> uint256:
    i = require_concrete(i, "BYTE(i, x) requires concrete i")
    if i > 31:
        return BW(0)
    start = 256 - (8 * i)
    return z3.Extract(start - 1, start - 8, x)


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
def SHA3(s: State, offset: uint256, size: uint256) -> uint256:
    offset = require_concrete(offset, "SHA3(offset, size) requires concrete offset")
    size = require_concrete(size, "SHA3(offset, size) requires concrete size")

    hash = keccak.new(digest_bits=256)
    for idx in range(offset, offset + size):
        data = s.memory.get(idx, 0)
        data = require_concrete(data, "SHA3(offset, size) requires concrete data")
        hash.update(data.to_bytes(1, "big"))
    return BW(int.from_bytes(hash.digest(), "big"))


# 30 - Get address of currently executing account
def ADDRESS(s: State) -> Address:
    return s.address


# 31 - Get balance of the given account
def BALANCE(w: World, address: Address) -> uint256:
    return w.balance(address)


# 32 - Get execution origination address
def ORIGIN(s: State) -> Address:
    return s.origin


# 33 - Get caller address
def CALLER(s: State) -> Address:
    return s.caller


# 34 - Get deposited value by the instruction/transaction responsible for this
# execution
def CALLVALUE(s: State) -> uint256:
    return s.callvalue


# 35 - Get input data of current environment
def CALLDATALOAD(s: State, i: uint256) -> uint256:
    return z3.Concat(*[s.calldata.get(i + j) for j in range(32)])


# 36 - Get size of input data in current environment
def CALLDATASIZE(s: State) -> uint256:
    return s.calldata.length()


# 37 - Copy input data in current environment to memory
def CALLDATACOPY(s: State, destOffset: uint256, offset: uint256, size: uint256) -> None:
    destOffset = require_concrete(
        destOffset,
        "CALLDATACOPY(destOffset, offset, size) requires concrete destOffset",
    )
    size = require_concrete(
        size, "CALLDATACOPY(destOffset, offset, size) requires concrete size"
    )
    for i in range(size):
        s.memory[destOffset + i] = s.calldata.get(offset + i)


# 38 - Get size of code running in current environment
def CODESIZE(s: State, w: World) -> uint256:
    address = require_concrete(s.address, "CODESIZE() requires concrete address")
    return BW(len(w.code(address)))


# 39 - Copy code running in current environment to memory
def CODECOPY(
    s: State, w: World, destOffset: uint256, offset: uint256, size: uint256
) -> None:
    destOffset = require_concrete(
        destOffset,
        "CODECOPY(destOffset, offset, size) requires concrete destOffset",
    )
    offset = require_concrete(
        offset, "CODECOPY(destOffset, offset, size) requires concrete offset"
    )
    size = require_concrete(
        size, "CODECOPY(destOffset, offset, size) requires concrete size"
    )
    address = require_concrete(
        s.address, "CODECOPY(destOffset, offset, size) requires concrete address"
    )
    code = w.code(address)
    for i in range(size):
        val = code[offset + i] if offset + i < len(code) else 0
        s.memory[destOffset + i] = BW(val)


# 3A - Get price of gas in current environment
def GASPRICE(s: State) -> uint256:
    return s.gasprice


# 3B - Get size of an account's code
def EXTCODESIZE(w: World, address: Address) -> uint256:
    address = require_concrete(
        address, "EXTCODESIZE(address) requires concrete address"
    )
    return BW(len(w.code(address)))


# 3C - Copy an account's code to memory
def EXTCODECOPY(
    s: State,
    w: World,
    address: Address,
    destOffset: uint256,
    offset: uint256,
    size: uint256,
) -> None:
    destOffset = require_concrete(
        destOffset,
        "EXTCODECOPY(address, destOffset, offset, size) requires concrete destOffset",
    )
    offset = require_concrete(
        offset,
        "EXTCODECOPY(address, destOffset, offset, size) requires concrete offset",
    )
    size = require_concrete(
        size, "EXTCODECOPY(address, destOffset, offset, size) requires concrete size"
    )
    address = require_concrete(
        address,
        "EXTCODECOPY(address, destOffset, offset, size) requires concrete address",
    )
    code = w.code(address)
    for i in range(size):
        val = code[offset + i] if offset + i < len(code) else 0
        s.memory[destOffset + i] = BW(val)


# 3D - Get size of output data from the previous call from the current
# environment
def RETURNDATASIZE(s: State) -> uint256:
    return BW(len(s.returndata))


# 3E - Copy output data from the previous call to memory
def RETURNDATACOPY(
    s: State, destOffset: uint256, offset: uint256, size: uint256
) -> None:
    destOffset = require_concrete(
        destOffset,
        "RETURNDATACOPY(destOffset, offset, size) requires concrete destOffset",
    )
    offset = require_concrete(
        offset, "RETURNDATACOPY(destOffset, offset, size) requires concrete offset"
    )
    size = require_concrete(
        size, "RETURNDATACOPY(destOffset, offset, size) requires concrete size"
    )
    for i in range(size):
        s.memory[destOffset + i] = (
            s.returndata[offset + i] if offset + i < len(s.returndata) else BW(0)
        )


# 3F - Get hash of an account's code
def EXTCODEHASH(w: World, address: Address) -> uint256:
    address = require_concrete(
        address,
        "EXTCODEHASH(address) requires concrete address",
    )
    code = w.code(address)
    if code == b"":
        return BW(0)

    hash = keccak.new(digest_bits=256)
    hash.update(code)
    return BW(int.from_bytes(hash.digest(), "big"))


# 40 - Get the hash of one of the 256 most recent complete blocks
def BLOCKHASH(b: Block, w: World, blockNumber: uint256) -> uint256:
    blockNumber = require_concrete(
        blockNumber, "BLOCKHASH(blockNumber) requires concrete blockNumber"
    )
    return z3.If(
        z3.Or(blockNumber >= b.number, blockNumber < b.number - 256),
        BW(0),
        BW(w.blockhash(blockNumber)),
    )


# 41 - Get the block's beneficiary address
def COINBASE(b: Block) -> Address:
    return b.coinbase


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
def SELFBALANCE(s: State, w: World) -> uint256:
    return w.balance(s.address)


# 48 - Get the base fee
def BASEFEE(b: Block) -> uint256:
    return b.basefee


# 50 - Remove item from stack
def POP(y: uint256) -> None:
    pass


# 51 - Load word from memory
def MLOAD(s: State, offset: uint256) -> uint256:
    offset = require_concrete(offset, "MLOAD(offset) requires concrete offset")
    return z3.Concat(*[s.memory.get(offset + i, BY(0)) for i in range(32)])


# 52 - Save word to memory
def MSTORE(s: State, offset: uint256, value: uint256) -> None:
    offset = require_concrete(offset, "MSTORE(offset, value) requires concrete offset")
    for i in range(31, -1, -1):
        s.memory[offset + i] = z3.Extract(7, 0, value)
        value = value >> 8


# 53 - Save byte to memory
def MSTORE8(s: State, offset: uint256, value: uint8) -> None:
    offset = require_concrete(offset, "MSTORE8(offset, value) requires concrete offset")
    s.memory[offset] = value & 0xFF


# 54 - Load word from storage
def SLOAD(s: State, key: uint256) -> uint256:
    return s.storage[key]


# 55 - Save word to storage
def SSTORE(s: State, key: uint256, value: uint256) -> None:
    s.storage = z3.Store(s.storage, key, value)


# 56 - Alter the program counter
def JUMP(s: State, counter: uint256) -> None:
    counter = require_concrete(counter, "JUMP(counter) requires concrete counter")
    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    s.pc = s.jumps[counter]


# 57 - Conditionally alter the program counter
def JUMPI(s: State, counter: uint256, b: uint256) -> None:
    counter = require_concrete(counter, "JUMPI(counter, b) requires concrete counter")
    b = require_concrete(b, "JUMPI(counter, b) requires concrete b")
    if b != 0:
        s.pc = s.jumps[counter]


# 5B - Marks a valid destination for jumps
def JUMPDEST() -> None:
    pass


# 59 - Get the size of active memory in bytes
def MSIZE(s: State) -> uint256:
    return BW(max(s.memory.keys()) + 1)


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


# TODO: F1 - CALL - Message-call into an account

# TODO: F2 - CALLCODE - Message-call into this account with alternative
# account's code


# F3 - Halts execution returning output data
def RETURN(s: State, offset: uint256, size: uint256) -> None:
    offset = require_concrete(
        offset,
        "RETURN(offset, size) requires concrete offset",
    )
    size = require_concrete(size, "RETURN(offset, size) requires concrete size")
    s.returndata = [s.memory.get(i, BW(0)) for i in range(offset, offset + size)]
    s.success = True


# TODO: F4 - DELEGATECALL - Message-call into this account with an alternative
# account’s code, but persisting the current values for sender and value

# TODO: FA - STATICCALL - Static message-call into an account


# FD - Halt execution reverting state changes but returning data and remaining
# gas
def REVERT(s: State, offset: uint256, size: uint256) -> None:
    offset = require_concrete(
        offset,
        "REVERT(offset, size) requires concrete offset",
    )
    size = require_concrete(size, "REVERT(offset, size) requires concrete size")
    s.returndata = [s.memory.get(i, BW(0)) for i in range(offset, offset + size)]
    s.success = False


# FE - Designated invalid instruction
def INVALID(s: State) -> None:
    s.returndata = []
    s.success = False


# TODO: 5A - GAS - Get the amount of available gas, including the corresponding
# reduction for the cost of this instruction

# TODO: F0 - CREATE - Create a new account with associated code

# TODO: F5 - CREATE2 - Create a new account with associated code at a
# predictable address

# TODO: FF - SELFDESTRUCT - Halt execution and register account for later
# deletion
