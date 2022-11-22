import contextlib
import copy
from dataclasses import dataclass, field
from typing import Any, Dict, Iterator, List, Optional, TypeAlias

import z3

uint8: TypeAlias = z3.BitVecRef
uint160: TypeAlias = z3.BitVecRef
uint256: TypeAlias = z3.BitVecRef


def BW(i: int) -> uint256:
    if i >= (1 << 256) or i < 0:
        raise ValueError(f"invalid word: {i}")
    return z3.BitVecVal(i, 256)


def BA(i: int) -> uint160:
    if i >= (1 << 160) or i < 0:
        raise ValueError(f"invalid address: {i}")
    return z3.BitVecVal(i, 160)


def BY(i: int) -> uint8:
    if i >= (1 << 8) or i < 0:
        raise ValueError(f"invalid byte: {i}")
    return z3.BitVecVal(i, 8)


class ByteArray:
    def __init__(self, name: str, data: bytes | None = None) -> None:
        self.arr = z3.Array(f"{name}", z3.BitVecSort(256), z3.BitVecSort(8))
        if data is None:
            self.len = z3.BitVec(f"{name}.length", 256)
        else:
            self.len = BW(len(data))
            for i, b in enumerate(data):
                self.arr = z3.Store(self.arr, i, b)

    def length(self) -> uint256:
        return self.len

    def get(self, i: uint256) -> uint8:
        return z3.If(i >= self.len, BY(0), self.arr[i])


class IntrospectableArray:
    def __init__(
        self, name: str, key: z3.BitVecSort, val: z3.Sort | z3.BitVecRef
    ) -> None:
        if isinstance(val, z3.SortRef):
            self.array = z3.Array(name, key, val)
        else:
            self.array = z3.K(key, val)
        self.accessed: List[z3.BitVecRef] = []
        self.written: List[z3.BitVecRef] = []

    def __getitem__(self, key: z3.BitVecRef) -> z3.BitVecRef:
        self.accessed.append(key)
        return self.array[key]

    def __setitem__(self, key: z3.BitVecRef, val: z3.BitVecRef) -> None:
        self.written.append(key)
        self.array = z3.Store(self.array, key, val)

    def copy(self) -> "IntrospectableArray":
        other = copy.copy(self)
        other.accessed = other.accessed.copy()
        other.written = other.written.copy()
        return other

    def copyreset(self) -> "IntrospectableArray":
        other = copy.copy(self)
        other.accessed = []
        other.written = []
        return other


@dataclass
class Opcode:
    code: int
    name: str
    fullName: str
    fee: int
    isAsync: bool
    dynamicGas: bool


@dataclass
class Instruction:
    # Start index of this instruction in the code, in bytes
    offset: int

    # Simplified instruction name, e.g. DUP1 -> DUP
    name: str

    # Numeric suffix, e.g. 1 for DUP1
    suffix: Optional[int] = None

    # Operand (PUSH only)
    operand: Optional[uint256] = None


@dataclass
class State:
    pc: int = 0
    jumps: Dict[int, int] = field(default_factory=dict)
    stack: List[uint256] = field(default_factory=list)
    memory: Dict[int, uint8] = field(
        default_factory=dict
    )  # concrete index -> 1-byte value
    address: uint160 = BA(0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    origin: uint160 = BA(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    caller: uint160 = BA(0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC)
    callvalue: uint256 = BW(0)
    calldata: ByteArray = ByteArray("CALLDATA", b"")
    gasprice: uint256 = BW(0x20)
    returndata: List[z3.BitVecRef] = field(default_factory=list)
    success: Optional[bool] = None

    storage: IntrospectableArray = IntrospectableArray(
        "STORAGE", z3.BitVecSort(256), BW(0)
    )

    # Maps the length of the input data to a Z3 Array which maps symbolic inputs
    # to symbolic hash digests.
    sha3hash: Dict[int, z3.Array] = field(default_factory=dict)
    sha3keys: List[z3.BitVec] = field(default_factory=list)

    # Global map of all account balances.
    balances: IntrospectableArray = IntrospectableArray(
        "BALANCES", z3.BitVecSort(160), BW(0)
    )

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    constraints: List[z3.ExprRef] = field(default_factory=list)

    # Additional constraints imposed by the multi-transaction solver.
    extra: List[z3.ExprRef] = field(default_factory=list)

    # Tracks the path of the program's execution. Each JUMPI is a bit, 1 if
    # taken, 0 if not. MSB-first with a leading 1 prepended.
    path: int = 1

    def transfer(self, src: uint160, dst: uint160, val: uint256) -> None:
        self.balances[src] -= val
        self.balances[dst] += val
        self.constraints.append(self.balances[src] >= 0)

    def copy(self) -> "State":
        return State(
            pc=self.pc,
            jumps=self.jumps,
            stack=self.stack.copy(),
            memory=self.memory.copy(),
            address=self.address,
            origin=self.origin,
            caller=self.caller,
            callvalue=self.callvalue,
            calldata=self.calldata,
            gasprice=self.gasprice,
            returndata=self.returndata,
            success=self.success,
            storage=self.storage.copy(),
            sha3hash=self.sha3hash.copy(),
            sha3keys=self.sha3keys.copy(),
            balances=self.balances.copy(),
            constraints=self.constraints.copy(),
            extra=self.extra.copy(),
            path=self.path,
        )

    def constrain(self, solver: z3.Optimize) -> None:
        solver.assert_and_track(self.address != self.origin, "ADDROR")
        # TODO: a contract could, in theory, call itself...
        solver.assert_and_track(self.address != self.caller, "ADDRCL")
        solver.assert_and_track(z3.And(*self.constraints), "PC")
        solver.assert_and_track(z3.And(*self.extra), "EXTRA")
        for i, k1 in enumerate(self.sha3keys):
            # TODO: this can still leave hash digests implausibly close to one
            # another, e.g. causing two arrays to overlap.
            solver.assert_and_track(
                z3.Extract(255, 128, self.sha3hash[k1.size()][k1]) != 0,
                f"SHA3.NLZ({i})",
            )
            for j, k2 in enumerate(self.sha3keys):
                if k1.size() != k2.size():
                    continue
                solver.assert_and_track(
                    z3.Implies(
                        k1 != k2,
                        self.sha3hash[k1.size()][k1] != self.sha3hash[k2.size()][k2],
                    ),
                    f"SHA3.DISTINCT({i},{j})",
                )

    def is_changed(self) -> bool:
        assert self.success is not None
        if self.success == False:
            # Ignore executions that REVERT, since they can't affect permanent
            # state.
            return False
        elif len(self.storage.written) > 0:
            # TODO: constrain further to eliminate no-op writes?
            return True
        elif len(self.balances.written) > 0:
            return True
        return False


@dataclass
class Block:
    number: uint256 = 0
    coinbase: uint256 = 0
    timestamp: uint256 = 0
    prevrandao: uint256 = 0
    gaslimit: uint256 = 0
    chainid: uint256 = 1
    basefee: uint256 = 0


@contextlib.contextmanager
def solver_stack(solver: z3.Solver) -> Iterator[None]:
    solver.push()
    try:
        yield
    finally:
        solver.pop()


def do_check(solver: z3.Solver, *assumptions: Any) -> bool:
    check = solver.check(*assumptions)
    if check == z3.sat:
        return True
    elif check == z3.unsat:
        return False
    else:
        raise Exception("z3 evaluation timed out")
