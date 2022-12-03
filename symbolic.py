"""Helpers for Z3 symbolic state."""

from __future__ import annotations

import contextlib
import copy
from typing import (
    Any,
    Iterator,
    List,
    Literal,
    Optional,
    TypeAlias,
    TypeGuard,
    Union,
    cast,
)

import z3
from Crypto.Hash import keccak

Constraint: TypeAlias = Union[z3.ExprRef, Literal[True], Literal[False]]

uint8: TypeAlias = z3.BitVecRef
uint160: TypeAlias = z3.BitVecRef
uint256: TypeAlias = z3.BitVecRef


def BW(i: int) -> uint256:
    """Convert an integer word into a 256-bit bitvector."""
    if i >= (1 << 256) or i < 0:
        raise ValueError(f"invalid word: {i}")
    return z3.BitVecVal(i, 256)


def BA(i: int) -> uint160:
    """Convert an integer address into a 160-bit bitvector."""
    if i >= (1 << 160) or i < 0:
        raise ValueError(f"invalid address: {i}")
    return z3.BitVecVal(i, 160)


def BY(i: int) -> uint8:
    """Convert an integer byte into an 8-bit bitvector."""
    if i >= (1 << 8) or i < 0:
        raise ValueError(f"invalid byte: {i}")
    return z3.BitVecVal(i, 8)


def is_concrete(value: z3.BitVecRef) -> TypeGuard[z3.BitVecNumRef]:
    """Check whether a given bitvector is concrete or symbolic."""
    return cast(bool, z3.is_bv_value(value))


def simplify(value: z3.ExprRef) -> z3.BitVecRef:
    """Simplify a bitvector expression."""
    value = z3.simplify(value)
    if not z3.is_bv(value):
        raise ValueError("unexpected non-bitvector")
    return cast(z3.BitVecRef, value)


def concretize(var: z3.ExprRef, msg: Optional[str] = None) -> int:
    """Unwrap a concrete bitvector expression into an int."""
    s = z3.simplify(var)
    if not z3.is_bv(s):
        raise ValueError("unexpected non-bitvector")
    if not z3.is_bv_value(s):
        raise ValueError(msg or "unexpected symbolic value")
    return cast(int, cast(z3.BitVecNumRef, s).as_long())


def concretize_hex(value: z3.BitVecRef) -> str:
    """Unwrap a concrete bitvector expression into a hex string."""
    value = simplify(value)
    return concretize(value).to_bytes(value.size() // 8, "big").hex()


def describe(value: z3.BitVecRef) -> str:
    """
    Produce a human-readable description of the given bitvector.

    For concrete bitvectors, returns a result in hexadecimal. Long values are
    broken into 256-bit chunks using dot syntax, e.g. "0x1234.1".

    For symbolic bitvectors, returns a hash based on the input variables.
    """
    value = simplify(value)
    if is_concrete(value):
        v: int = concretize(value)
        p = []
        while v > 0:
            b = v & ((1 << 256) - 1)
            p.append(hex(b)[2:])
            v >>= 256
        return "0x" + ".".join(reversed(p))
    else:
        digest = keccak.new(data=str(value).encode(), digest_bits=256).digest()
        return "#" + digest[:3].hex()


class Bytes:
    """A symbolic, unknown-length sequence of immutable bytes."""

    def __init__(self, name: str, data: bytes | None = None) -> None:
        """Create a new Bytes."""
        self.arr = z3.Array(f"{name}", z3.BitVecSort(256), z3.BitVecSort(8))
        if data is None:
            self.len = z3.BitVec(f"{name}.length", 256)
        else:
            self.len = BW(len(data))
            for i, b in enumerate(data):
                self.arr = cast(z3.ArrayRef, z3.Store(self.arr, i, b))

    def length(self) -> uint256:
        """Return the symbolic length of the bytestring."""
        return self.len

    def get(self, i: uint256) -> uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        return cast(uint8, z3.If(i >= self.len, BY(0), self.arr[i]))


class Array:
    """
    A symbolic array.

    Represented as a Z3 Array, i.e. an uninterpreted function from the given
    domain to the given codomain.

    Tracks which keys are accessed and written.
    """

    def __init__(
        self, name: str, key: z3.BitVecSortRef, val: z3.SortRef | z3.BitVecRef
    ) -> None:
        """Create a new Array."""
        if isinstance(val, z3.SortRef):
            self.array = z3.Array(name, key, val)
        else:
            self.array = z3.K(key, val)
        self.accessed: List[z3.BitVecRef] = []
        self.written: List[z3.BitVecRef] = []

    def __getitem__(self, key: z3.BitVecRef) -> z3.BitVecRef:
        """Look up the given symbolic key."""
        self.accessed.append(key)
        return cast(z3.BitVecRef, self.array[key])

    def __setitem__(self, key: z3.BitVecRef, val: z3.BitVecRef) -> None:
        """Set the given symbolic key to the given symbolic value."""
        self.written.append(key)
        self.array = cast(z3.ArrayRef, z3.Store(self.array, key, val))

    def copy(self) -> Array:
        """Return a deep copy of this instance."""
        other = copy.copy(self)
        other.accessed = other.accessed.copy()
        other.written = other.written.copy()
        return other


@contextlib.contextmanager
def solver_stack(solver: z3.Optimize) -> Iterator[None]:
    """Create a nested Z3 context using push()/pop()."""
    solver.push()
    try:
        yield
    finally:
        solver.pop()


def check(solver: z3.Optimize, *assumptions: Any) -> bool:
    """
    Check whether the given Z3 solver state is satisfiable.

    Returns true or false. Raises an error if Z3 fails.
    """
    check = solver.check(*assumptions)
    if check == z3.sat:
        return True
    elif check == z3.unsat:
        return False
    else:
        raise Exception(f"z3 failure: {solver.reason_unknown()}")
