from dataclasses import dataclass, field
from typing import Dict, List, Optional, TypeAlias

import z3

uint8: TypeAlias = z3.BitVecRef
uint256: TypeAlias = z3.BitVecRef
Address: TypeAlias = z3.BitVecRef


def BW(i: int) -> uint256:
    if i >= (1 << 256) or i < 0:
        raise ValueError(f"invalid word: {i}")
    return z3.BitVecVal(i, 256)


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
    address: Address = (
        BW(0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA),
    )
    origin: Address = (
        BW(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB),
    )
    caller: Address = (
        BW(0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC),
    )
    callvalue: uint256 = BW(0)
    calldata: ByteArray = ByteArray("CALLDATA", b"")
    gasprice: uint256 = BW(0x20)
    returndata: List[z3.BitVecRef] = field(default_factory=list)
    success: Optional[bool] = None
    storage: z3.Array = z3.K(z3.BitVecSort(256), BW(0))

    # It's difficult to extract the list of set keys when Z3 solves for the
    # storage array. Instead, we track which keys have been accessed here.
    storagekeys: List[z3.BitVec] = field(default_factory=list)

    # Maps the length of the input data to a Z3 Array which maps symbolic inputs
    # to symbolic hash digests.
    sha3hash: Dict[int, z3.Array] = field(default_factory=dict)
    sha3keys: List[z3.BitVec] = field(default_factory=list)

    # Global map of all account balances.
    balances: z3.Array = z3.K(z3.BitVecSort(256), BW(0))

    # List of Z3 expressions that must be satisfied in order for the program to
    # reach this state. Based on the JUMPI instructions (if statements) seen so
    # far.
    constraints: List[z3.ExprRef] = field(default_factory=list)

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
            storage=self.storage,
            storagekeys=self.storagekeys.copy(),
            sha3hash=self.sha3hash.copy(),
            sha3keys=self.sha3keys.copy(),
            constraints=self.constraints.copy(),
        )

    def constrain(self, solver: z3.Optimize) -> None:
        solver.assert_and_track(z3.And(*self.constraints), "PC")
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


@dataclass
class Block:
    number: uint256 = 0
    coinbase: Address = 0
    timestamp: uint256 = 0
    prevrandao: uint256 = 0
    gaslimit: uint256 = 0
    chainid: uint256 = 1
    basefee: uint256 = 0
