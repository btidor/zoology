import typing
from abc import ABC, abstractmethod
from dataclasses import dataclass, field

from Crypto.Hash import keccak

uint256 = int
Address = int

MAX = 1 << 256


@dataclass
class State:
    pc: typing.Optional[int] = None
    memory: typing.Dict[int, int] = field(default_factory=dict)  # index -> 1-byte value
    address: Address = 0
    origin: Address = 0
    caller: Address = 0
    callvalue: uint256 = 0
    calldata: bytes = b""
    gasprice: uint256 = 0
    returndata: bytes = b""


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
    def blockhash(self, blockNumber: uint256) -> uint256:
        pass


def _twos_complement(x: uint256) -> uint256:
    if x < 0:
        return (-x ^ (MAX - 1)) + 1
    elif x & (1 << 255):
        return -1 * ((x ^ (MAX - 1)) + 1)
    else:
        return x


# 00 - Halts execution
def STOP(s: State) -> None:
    s.pc = None


# 01 - Addition operation
def ADD(a: uint256, b: uint256) -> uint256:
    return (a + b) % MAX


# 02 - Multiplication operation
def MUL(a: uint256, b: uint256) -> uint256:
    return (a * b) % MAX


# 03 - Subtraction operation
def SUB(a: uint256, b: uint256) -> uint256:
    return (a - b) % MAX


# 04 - Integer division operation
def DIV(a: uint256, b: uint256) -> uint256:
    if b == 0:
        return 0
    return a // b


# 05 - Signed integer division operation (truncated)
def SDIV(a: uint256, b: uint256) -> uint256:
    if b == 0:
        return 0

    a = _twos_complement(a)
    b = _twos_complement(b)
    return _twos_complement(a // b)


# 06 - Modulo remainder operation
def MOD(a: uint256, b: uint256) -> uint256:
    if b == 0:
        return 0
    return a % b


# 07 - Signed modulo remainder operation
def SMOD(a: uint256, b: uint256) -> uint256:
    if b == 0:
        return 0

    a = _twos_complement(a)
    b = _twos_complement(b)
    return _twos_complement(a % b)


# 08 - Modulo addition operation
def ADDMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    if N == 0:
        return 0
    return (a + b) % N


# 09 - Modulo multiplication operation
def MULMOD(a: uint256, b: uint256, N: uint256) -> uint256:
    if N == 0:
        return 0
    return (a * b) % N


# 0A - Exponential operation
def EXP(a: uint256, exponent: uint256) -> uint256:
    # Python types this as 'Any' because if exponent were negative, the result
    # will be a float (https://stackoverflow.com/a/64096587).
    return typing.cast(int, a**exponent) % MAX


# 0B - Extend length of two's complement signed integer
def SIGNEXTEND(b: uint256, x: uint256) -> uint256:
    bits = (b + 1) * 8
    if x & (1 << (bits - 1)) == 0:
        return x
    return ((MAX - 1) ^ ((1 << bits) - 1)) | x


# 10 - Less-than comparison
def LT(a: uint256, b: uint256) -> uint256:
    return 1 if a < b else 0


# 11 - Greater-than comparison
def GT(a: uint256, b: uint256) -> uint256:
    return 1 if a > b else 0


# 12 - Signed less-than comparison
def SLT(a: uint256, b: uint256) -> uint256:
    a = _twos_complement(a)
    b = _twos_complement(b)
    return 1 if a < b else 0


# 13 - Signed greater-than comparison
def SGT(a: uint256, b: uint256) -> uint256:
    a = _twos_complement(a)
    b = _twos_complement(b)
    return 1 if a > b else 0


# 14 - Equality comparison
def EQ(a: uint256, b: uint256) -> uint256:
    return 1 if a == b else 0


# 15 - Simple not operator
def ISZERO(a: uint256) -> uint256:
    return 1 if a == 0 else 0


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
    return a ^ (MAX - 1)


# 1A - Retrieve single bytes from word
def BYTE(i: uint256, x: uint256) -> uint256:
    if i > 31:
        return 0
    return (x >> (8 * (31 - i))) & 0xFF


# 1B - Left shift operation
def SHL(shift: uint256, value: uint256) -> uint256:
    return (value << shift) & (MAX - 1)


# 1C - Logical right shift operation
def SHR(shift: uint256, value: uint256) -> uint256:
    return value >> shift


# 1D - Arithmetic (signed) right shift operation
def SAR(shift: uint256, value: uint256) -> uint256:
    value = _twos_complement(value)
    return _twos_complement(value >> shift)


# 20 - Compute Keccak-256 hash
def SHA3(s: State, offset: uint256, size: uint256) -> uint256:
    hash = keccak.new(digest_bits=256)
    for idx in range(offset, offset + size):
        data = s.memory.get(idx, 0).to_bytes(1, "big")
        hash.update(data)
    return int.from_bytes(hash.digest(), "big")


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
    if i >= len(s.calldata):
        return 0
    extended = s.calldata + (b"\x00" * 32)
    return int.from_bytes(extended[i : i + 32], "big")


# 36 - Get size of input data in current environment
def CALLDATASIZE(s: State) -> uint256:
    return len(s.calldata)


# 37 - Copy input data in current environment to memory
def CALLDATACOPY(s: State, destOffset: uint256, offset: uint256, size: uint256) -> None:
    for i in range(size):
        val = s.calldata[offset + i] if offset + i < len(s.calldata) else 0
        s.memory[destOffset + i] = val


# 38 - Get size of code running in current environment
def CODESIZE(s: State, w: World) -> uint256:
    return len(w.code(s.address))


# 39 - Copy code running in current environment to memory
def CODECOPY(
    s: State, w: World, destOffset: uint256, offset: uint256, size: uint256
) -> None:
    code = w.code(s.address)
    for i in range(size):
        val = code[offset + i] if offset + i < len(code) else 0
        s.memory[destOffset + i] = val


# 3A - Get price of gas in current environment
def GASPRICE(s: State) -> uint256:
    return s.gasprice


# 3B - Get size of an account's code
def EXTCODESIZE(w: World, address: Address) -> uint256:
    return len(w.code(address))


# 3C - Copy an account's code to memory
def EXTCODECOPY(
    s: State,
    w: World,
    address: Address,
    destOffset: uint256,
    offset: uint256,
    size: uint256,
) -> None:
    code = w.code(address)
    for i in range(size):
        val = code[offset + i] if offset + i < len(code) else 0
        s.memory[destOffset + i] = val


# 3D - Get size of output data from the previous call from the current
# environment
def RETURNDATASIZE(s: State) -> uint256:
    return len(s.returndata)


# 3E - Copy output data from the previous call to memory
def RETURNDATACOPY(
    s: State, destOffset: uint256, offset: uint256, size: uint256
) -> None:
    for i in range(size):
        val = s.returndata[offset + i] if offset + i < len(s.returndata) else 0
        s.memory[destOffset + i] = val


# 3F - Get hash of an account's code
def EXTCODEHASH(w: World, address: Address) -> uint256:
    code = w.code(address)
    if code == b"":
        return 0

    hash = keccak.new(digest_bits=256)
    hash.update(code)
    return int.from_bytes(hash.digest(), "big")


# 40 - Get the hash of one of the 256 most recent complete blocks
def BLOCKHASH(b: Block, w: World, blockNumber: uint256) -> uint256:
    if blockNumber >= b.number or blockNumber < b.number - 256:
        return 0
    return w.blockhash(blockNumber)


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
