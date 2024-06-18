"""A library of EVM instruction implementations."""

import copy
from inspect import Signature, signature
from typing import Any, Literal

from bytes import Bytes
from disassembler import Instruction
from opcodes import REFERENCE, SPECIAL, UNIMPLEMENTED
from smt import (
    Constraint,
    Int,
    Uint,
    Uint8,
    Uint160,
    Uint256,
    bvlshr_harder,
    concat_bytes,
)
from state import (
    Address,
    Block,
    Blockchain,
    HyperCall,
    HyperCreate,
    Runtime,
    Transaction,
)

Int256 = Int[Literal[256]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

type Fork = tuple[Runtime, Runtime]
type Terminate = tuple[bool, Bytes]
type OpResult = None | Uint256 | Fork | Terminate


def STOP() -> Terminate:
    """00 - Halts execution."""
    return (True, Bytes())


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


def KECCAK256(r: Runtime, offset: Uint256, size: Uint256) -> Uint256:
    """20 - Compute Keccak-256 (SHA3) hash."""
    return r.path.keccak256(r.memory.slice(offset, size))


def ADDRESS(tx: Transaction) -> Uint256:
    """30 - Get address of currently executing account."""
    return tx.address.into(Uint256)


def BALANCE(k: Blockchain, address: Uint256) -> Uint256:
    """31 - Get balance of the given account."""
    return k.balances[address.into(Uint160)]


def ORIGIN(tx: Transaction) -> Uint256:
    """32 - Get execution origination address."""
    return tx.origin.into(Uint256)


def CALLER(tx: Transaction) -> Uint256:
    """33 - Get caller address."""
    return tx.caller.into(Uint256)


def CALLVALUE(tx: Transaction) -> Uint256:
    """
    34.

    Get deposited value by the instruction/transaction responsible for this
    execution.
    """
    return tx.callvalue


def CALLDATALOAD(tx: Transaction, i: Uint256) -> Uint256:
    """35 - Get input data of current environment."""
    return concat_bytes(*[tx.calldata[i + Uint256(j)] for j in range(32)])


def CALLDATASIZE(tx: Transaction) -> Uint256:
    """36 - Get size of input data in current environment."""
    return tx.calldata.length


def CALLDATACOPY(
    r: Runtime, tx: Transaction, destOffset: Uint256, offset: Uint256, size: Uint256
) -> None:
    """37 - Copy input data in current environment to memory."""
    r.memory.graft(tx.calldata.slice(offset, size), destOffset)


def CODESIZE(r: Runtime) -> Uint256:
    """38 - Get size of code running in current environment."""
    return r.program.code.length


def CODECOPY(r: Runtime, destOffset: Uint256, offset: Uint256, size: Uint256) -> None:
    """39 - Copy code running in current environment to memory."""
    r.memory.graft(r.program.code.slice(offset, size), destOffset)


def GASPRICE(tx: Transaction) -> Uint256:
    """3A - Get price of gas in current environment."""
    return tx.gasprice


def EXTCODESIZE(k: Blockchain, address: Uint256) -> Uint256:
    """3B - Get size of an account's code."""
    result = Uint256(0)
    for a, contract in k.contracts.items():
        result = (address.into(Uint160) == Uint160(a)).ite(
            contract.program.code.length, result
        )
    # TODO: consider mystery proxy as well
    return result


def EXTCODECOPY(
    k: Blockchain,
    r: Runtime,
    address: Uint256,
    destOffset: Uint256,
    offset: Uint256,
    size: Uint256,
) -> None:
    """3C - Copy an account's code to memory."""
    raise NotImplementedError("EXTCODECOPY")


def RETURNDATASIZE(r: Runtime) -> Uint256:
    """
    3D.

    Get size of output data from the previous call from the current environment.
    """
    return r.latest_return.length


def RETURNDATACOPY(
    r: Runtime, destOffset: Uint256, offset: Uint256, size: Uint256
) -> None:
    """3E - Copy output data from the previous call to memory."""
    r.memory.graft(r.latest_return.slice(offset, size), destOffset)


def EXTCODEHASH(k: Blockchain, r: Runtime, address: Uint256) -> Uint256:
    """3F - Get hash of an account's code."""
    key = Address.unwrap(address.into(Uint160), "EXTCODEHASH")
    if key in k.contracts:
        return r.path.keccak256(k.contracts[key].program.code)
    else:
        # Properly, EXTCODEHASH should return zero if the address does not exist
        # or is empty, and the empty hash otherwise.
        raise NotImplementedError  # see EIP-1052


def BLOCKHASH(blk: Block, blockNumber: Uint256) -> Uint256:
    """40 - Get the hash of one of the 256 most recent complete blocks."""
    offset = Uint256(256) - blk.number + blockNumber
    return (offset < Uint256(256)).ite(blk.hashes[offset.into(Uint8)], Uint256(0))


def COINBASE(blk: Block) -> Uint256:
    """41 - Get the block's beneficiary address."""
    return blk.coinbase.into(Uint256)


def TIMESTAMP(blk: Block) -> Uint256:
    """42 - Get the block's timestamp."""
    return blk.timestamp


def NUMBER(blk: Block) -> Uint256:
    """43 - Get the block's number."""
    return blk.number


def PREVRANDAO(blk: Block) -> Uint256:
    """44 - Get the previous block's RANDAO mix."""
    return blk.prevrandao


def GASLIMIT(blk: Block) -> Uint256:
    """45 - Get the block's gas limit."""
    return blk.gaslimit


def CHAINID(blk: Block) -> Uint256:
    """46 - Get the chain ID."""
    return blk.chainid


def SELFBALANCE(k: Blockchain, tx: Transaction) -> Uint256:
    """47 - Get balance of currently executing account."""
    return k.balances[tx.address]


def BASEFEE(blk: Block) -> Uint256:
    """48 - Get the base fee."""
    return blk.basefee


def POP(y: Uint256) -> None:
    """50 - Remove item from stack."""
    pass


def MLOAD(r: Runtime, offset: Uint256) -> Uint256:
    """51 - Load word from memory."""
    return concat_bytes(*[r.memory[offset + Uint256(i)] for i in range(32)])


def MSTORE(r: Runtime, offset: Uint256, value: Uint256) -> None:
    """52 - Save word to memory."""
    r.memory.setword(offset, value)


def MSTORE8(r: Runtime, offset: Uint256, value: Uint256) -> None:
    """53 - Save byte to memory."""
    r.memory[offset] = value.into(Uint8)


def SLOAD(r: Runtime, key: Uint256) -> Uint256:
    """54 - Load word from storage."""
    return r.storage[key]


def SSTORE(r: Runtime, key: Uint256, value: Uint256) -> None:
    """55 - Save word to storage."""
    r.path.static = False
    r.storage[key] = value


def JUMP(r: Runtime, counter: Uint256) -> None:
    """56 - Alter the program counter."""
    j = counter.reveal()
    assert j is not None, "JUMP requires concrete counter"

    # In theory, JUMP should revert if counter is not a valid jump target.
    # Instead, raise an error and fail the whole analysis. This lets us prove
    # that all jump targets are valid and within the body of the code, which is
    # why it's safe to strip the metadata trailer.
    r.pc = r.program.jumps[j]


def JUMPI(r: Runtime, ins: Instruction, counter: Uint256, b: Uint256) -> Fork | None:
    """57 - Conditionally alter the program counter."""
    j = counter.reveal()
    assert j is not None, "JUMPI requires concrete counter"

    r.path.id <<= 1
    c = b == Uint256(0)
    match c.reveal():
        case None:  # unknown, must prepare both branches :(
            r0, r1 = copy.deepcopy(r), r
            r0.path.constraint &= c

            r1.pc = r.program.jumps[j]
            r1.path.id |= 1
            r1.path.constraint &= ~c
            return (r0, r1)
        case True:  # branch never taken, fall through
            return None
        case False:  # branch always taken
            r.pc = r.program.jumps[j]
            r.path.id |= 1
            return None


def PC(ins: Instruction) -> Uint256:
    """
    58.

    Get the value of the program counter prior to the increment corresponding to
    this instruction.
    """
    return Uint256(ins.offset)


def MSIZE(r: Runtime) -> Uint256:
    """59 - Get the size of active memory in bytes."""
    return r.memory.length


def GAS(r: Runtime) -> Uint256:
    """
    5A.

    Get the amount of available gas, including the corresponding reduction for
    the cost of this instruction.

    Since we don't actually track gas usage, return either a symbolic value or a
    concrete dummy value based on the execution mode.
    """
    return Uint256("TODO")


def JUMPDEST() -> None:
    """5B - Marks a valid destination for jumps."""
    pass


def PUSH(ins: Instruction) -> Uint256:
    """6X/7X - Place N byte item on stack."""
    if not isinstance(ins.operand, Uint):
        raise ValueError("somehow got a PUSH without an operand")
    return ins.operand


def DUP(ins: Instruction, r: Runtime) -> Uint256:
    """8X - Duplicate Nth stack item."""
    if ins.suffix is None:
        raise ValueError("somehow got a DUP without a suffix")
    return r.stack[-ins.suffix]


def SWAP(ins: Instruction, r: Runtime) -> None:
    """9X - Exchange 1st and (N+1)th stack items."""
    if ins.suffix is None:
        raise ValueError("somehow got a SWAP without a suffix")
    m = ins.suffix + 1
    r.stack[-1], r.stack[-m] = r.stack[-m], r.stack[-1]


def LOG(ins: Instruction, r: Runtime, offset: Uint256, size: Uint256) -> None:
    """AX - Append log record with N topics."""
    r.path.static = False
    if ins.suffix is None:
        raise ValueError("somehow got a LOG without a suffix")
    for _ in range(ins.suffix):
        r.stack.pop()  # we don't actually save the log entries anywhere


def CREATE(
    r: Runtime, tx: Transaction, value: Uint256, offset: Uint256, size: Uint256
) -> Uint256:
    """F0 - Create a new account with associated code."""
    r.path.static = False
    hyper = HyperCreate(
        callvalue=value,
        initcode=r.memory.slice(offset, size),
        salt=None,
        address=Uint160(f"CREATE{len(r.hyper)}"),
    )
    r.hyper.append(hyper)
    return hyper.address.into(Uint256)


def CALL(
    r: Runtime,
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """F1 - Message-call into an account."""
    if value.reveal() != 0:  # TODO: this is a big hack
        r.path.static = False
    success = Constraint(f"CALLOK{len(r.hyper)}")
    returndata = Bytes.symbolic(f"CALLRET{len(r.hyper)}")
    hyper = HyperCall(
        gas,
        address.into(Uint160),
        value,
        r.memory.slice(argsOffset, argsSize),
        success,
        returndata,
    )
    r.hyper.append(hyper)
    r.latest_return = returndata
    r.memory.graft(returndata.slice(Uint256(0), retSize), retOffset)
    return success.ite(Uint256(1), Uint256(0))


def CALLCODE(
    r: Runtime,
    gas: Uint256,
    address: Uint256,
    value: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """F2 - Message-call into this account with alternative account's code."""
    raise NotImplementedError("CALLCODE")


def RETURN(r: Runtime, offset: Uint256, size: Uint256) -> Terminate:
    """F3 - Halts execution returning output data."""
    return (True, r.memory.slice(offset, size))


def DELEGATECALL(
    r: Runtime,
    tx: Transaction,
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
    """
    success = Constraint(f"CALLOK{len(r.hyper)}")
    returndata = Bytes.symbolic(f"CALLRET{len(r.hyper)}")
    hyper = HyperCall(
        gas,
        address.into(Uint160),
        tx.callvalue,
        r.memory.slice(argsOffset, argsSize),
        success,
        returndata,
        delegate=True,
    )
    r.hyper.append(hyper)
    r.latest_return = returndata
    r.memory.graft(returndata.slice(Uint256(0), retSize), retOffset)
    return success.ite(Uint256(1), Uint256(0))


def CREATE2(
    r: Runtime,
    tx: Transaction,
    value: Uint256,
    offset: Uint256,
    size: Uint256,
    salt: Uint256,
) -> Uint256:
    """F5 - Create a new account with associated code at a predictable address."""
    r.path.static = False
    hyper = HyperCreate(
        callvalue=value,
        initcode=r.memory.slice(offset, size),
        salt=salt,
        address=Uint160(f"CREATE{len(r.hyper)}"),
    )
    r.hyper.append(hyper)
    return hyper.address.into(Uint256)


def STATICCALL(
    r: Runtime,
    gas: Uint256,
    address: Uint256,
    argsOffset: Uint256,
    argsSize: Uint256,
    retOffset: Uint256,
    retSize: Uint256,
) -> Uint256:
    """FA - Static message-call into an account."""
    success = Constraint(f"CALLOK{len(r.hyper)}")
    returndata = Bytes.symbolic(f"CALLRET{len(r.hyper)}")
    hyper = HyperCall(
        gas,
        address.into(Uint160),
        Uint256(0),
        r.memory.slice(argsOffset, argsSize),
        success,
        returndata,
        static=True,
    )
    r.hyper.append(hyper)
    r.latest_return = returndata
    r.memory.graft(returndata.slice(Uint256(0), retSize), retOffset)
    return success.ite(Uint256(1), Uint256(0))


def REVERT(r: Runtime, offset: Uint256, size: Uint256) -> Terminate:
    """
    FD.

    Halt execution reverting state changes but returning data and remaining gas.
    """
    return (False, r.memory.slice(offset, size))


def INVALID(r: Runtime) -> Terminate:
    """FE - Designated invalid instruction."""
    return (False, Bytes())


def SELFDESTRUCT(r: Runtime, tx: Transaction, address: Uint256) -> None:
    """FF - Halt execution and register account for later deletion."""
    r.path.static = False
    raise NotImplementedError("SELFDESTRUCT")


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
