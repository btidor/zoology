from abc import ABC, abstractmethod, abstractproperty
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
    memory: Dict[int, uint8] = field(
        default_factory=dict
    )  # concrete index -> 1-byte value
    address: Address = z3.BitVec("ADDRESS", 256)
    origin: Address = z3.BitVec("ORIGIN", 256)
    caller: Address = z3.BitVec("CALLER", 256)
    callvalue: uint256 = z3.BitVec("CALLVALUE", 256)
    calldata: ByteArray = ByteArray("CALLDATA")
    gasprice: uint256 = z3.BitVec("GASPRICE", 256)
    returndata: List[z3.BitVecRef] = field(default_factory=list)
    success: Optional[bool] = None
    storage: z3.Array = z3.Array("STORAGE", z3.BitVecSort(256), z3.BitVecSort(256))
    constraints: z3.ExprRef = z3.BoolVal(True)

    def copy(self) -> "State":
        return State(
            pc=self.pc,
            jumps=self.jumps,
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
            constraints=self.constraints,
        )
