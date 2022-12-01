import contextlib
import copy
from typing import Any, Iterator, List, Optional, TypeAlias, cast

import z3


def require_concrete(var: z3.ExprRef, msg: Optional[str] = None) -> int:
    s = z3.simplify(var)
    if not z3.is_bv(s):
        raise ValueError("unexpected non-bitvector")
    if not z3.is_bv_value(s):
        raise ValueError(msg or "unexpected symbolic value")
    return cast(int, cast(z3.BitVecNumRef, s).as_long())


def hexify(value: z3.ExprRef, length: int) -> str:
    value = z3.simplify(value)
    if not z3.is_bv(value):
        raise ValueError("unexpected non-bitvector")
    if not z3.is_bv_value(value):
        raise ValueError("unexpected symbolic value")
    return (
        cast(int, cast(z3.BitVecNumRef, value).as_long()).to_bytes(length, "big").hex()
    )


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
                self.arr = cast(z3.ArrayRef, z3.Store(self.arr, i, b))

    def length(self) -> uint256:
        return self.len

    def get(self, i: uint256) -> uint8:
        return cast(uint8, z3.If(i >= self.len, BY(0), self.arr[i]))


class IntrospectableArray:
    def __init__(
        self, name: str, key: z3.BitVecSortRef, val: z3.SortRef | z3.BitVecRef
    ) -> None:
        if isinstance(val, z3.SortRef):
            self.array = z3.Array(name, key, val)
        else:
            self.array = z3.K(key, val)
        self.accessed: List[z3.BitVecRef] = []
        self.written: List[z3.BitVecRef] = []

    def __getitem__(self, key: z3.BitVecRef) -> z3.BitVecRef:
        self.accessed.append(key)
        return cast(z3.BitVecRef, self.array[key])

    def __setitem__(self, key: z3.BitVecRef, val: z3.BitVecRef) -> None:
        self.written.append(key)
        self.array = cast(z3.ArrayRef, z3.Store(self.array, key, val))

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


@contextlib.contextmanager
def solver_stack(solver: z3.Optimize) -> Iterator[None]:
    solver.push()
    try:
        yield
    finally:
        solver.pop()


def do_check(solver: z3.Optimize, *assumptions: Any) -> bool:
    check = solver.check(*assumptions)
    if check == z3.sat:
        return True
    elif check == z3.unsat:
        return False
    else:
        raise Exception(f"z3 failure: {solver.reason_unknown()}")
