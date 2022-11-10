import typing

from common import Context

uint256 = int

MAX = 1 << 256


def _twos_complement(x: uint256) -> uint256:
    if x < 0:
        return (-x ^ (MAX - 1)) + 1
    elif x & (1 << 255):
        return -1 * ((x ^ (MAX - 1)) + 1)
    else:
        return x


# 00 - Halts execution
def STOP(c: Context) -> None:
    c.pc = None


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
