"""A library of EVM instruction implementations."""

import copy
from inspect import Signature, signature
from typing import Any, Literal

from bytes import Bytes
from disassembler import CustomCopy, Instruction
from opcodes import REFERENCE, SPECIAL, UNIMPLEMENTED
from smt import (
    Int,
    Uint,
    Uint8,
    Uint160,
    Uint256,
    bvlshr_harder,
    concat_bytes,
    overflow_safe,
    substitute,
)
from state import State, Termination

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
    return s.balance[address.into(Uint160)]


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


def EXTCODESIZE(s: State, address: Uint256) -> Uint256:
    """3B - Get size of an account's code."""
    raise NotImplementedError(".sym")


def EXTCODECOPY(
    s: State, address: Uint256, destOffset: Uint256, offset: Uint256, size: Uint256
) -> None:
    """3C - Copy an account's code to memory."""
    raise NotImplementedError("EXTCODECOPY")


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
    raise NotImplementedError(".sym")


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
    return s.balance[s.transaction.address]


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
    s.static = False
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
) -> tuple[State, State] | None:
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
            return (s0, s1)
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
    raise NotImplementedError(".sym")


def JUMPDEST() -> None:
    """5B - Marks a valid destination for jumps."""
    pass


def PUSH(ins: Instruction) -> Uint256:
    """6X/7X - Place N byte item on stack."""
    if not isinstance(ins.operand, Uint):
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
    s.static = False
    if ins.suffix is None:
        raise ValueError("somehow got a LOG without a suffix")
    raise NotImplementedError("LOG")


def CREATE(s: State, value: Uint256, offset: Uint256, size: Uint256) -> None:
    """F0 - Create a new account with associated code."""
    raise NotImplementedError(".sym")


def CALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> None:
    """F1 - Message-call into an account."""
    raise NotImplementedError(".sym")


def CALLCODE(
    s: State,
    gas: Uint256,
    _address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> None:
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
) -> None:
    """
    F4.

    Message-call into this account with an alternative account's code, but
    persisting the current values for sender and value.
    """
    raise NotImplementedError(".sym")


def CREATE2(
    s: State, value: Uint256, offset: Uint256, size: Uint256, _salt: Uint256
) -> None:
    """F5 - Create a new account with associated code at a predictable address."""
    raise NotImplementedError(".sym")


def STATICCALL(
    s: State,
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> None:
    """FA - Static message-call into an account."""
    raise NotImplementedError(".sym")


def REVERT(s: State, offset: Uint256, size: Uint256) -> None:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    s.pc = Termination(False, s.memory.slice(offset, size))


def INVALID(s: State) -> None:
    """FE - Designated invalid instruction."""
    s.pc = Termination(False, Bytes())


def SELFDESTRUCT(s: State, address: Uint256) -> None:
    """FF - Halt execution and register account for later deletion."""
    s.static = False

    contract = s.transaction.address
    recipient = address.into(Uint160)
    value = s.balance[contract]

    # Note: if `current` and `recipient` are equal, the value disappears.
    s.balance[recipient] += value
    s.constraint &= overflow_safe(s.balance[recipient], value)
    s.balance[contract] = Uint256(0)

    # TODO
    # assert (c := contract.reveal()) is not None
    # s.contracts[c].destructed = True

    s.pc = Termination(True, Bytes())


def CUSTOM(s: State, ins: Instruction) -> None:
    """XX - Implement custom logic for loop flattening."""
    if not isinstance(ins.operand, CustomCopy):
        raise ValueError("CUSTOM requires a descriptor operand")

    stack = list(reversed(s.stack))
    substitutions = list((Uint256(f"STACK{i}"), stack[i]) for i in range(8))
    start = substitute(ins.operand.start, substitutions)
    end = substitute(ins.operand.end, substitutions)
    stride = substitute(ins.operand.stride, substitutions)
    read = substitute(ins.operand.read, substitutions)
    write = substitute(ins.operand.write, substitutions)

    if stride.reveal() != 0x20:
        raise NotImplementedError(f"unsupported stride length: {stride}")

    s.memory.graft(
        s.memory.slice(read + start, end - start),
        write + start,
    )
    s.stack.pop()
    s.stack.append(end)
    s.pc = s.program.jumps[ins.operand.exit]


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
