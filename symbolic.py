"""Helpers for Z3 symbolic state."""

from __future__ import annotations

import contextlib
from typing import (
    Any,
    Dict,
    Iterable,
    Iterator,
    List,
    Literal,
    Optional,
    TypeAlias,
    TypeGuard,
    TypeVar,
    Union,
    cast,
)

import z3
from Crypto.Hash import keccak

K = TypeVar("K")


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


def simplify(value: z3.BitVecRef) -> z3.BitVecRef:
    """Simplify a bitvector expression."""
    return cast(z3.BitVecRef, z3.simplify(value))


def unwrap(value: z3.BitVecRef, msg: Optional[str] = None) -> int:
    """Unwrap a concrete bitvector expression into an int."""
    value = simplify(value)
    if not is_concrete(value):
        raise ValueError(msg or "unexpected symbolic value")
    return cast(int, value.as_long())


def unwrap_bytes(value: z3.BitVecRef, msg: Optional[str] = None) -> bytes:
    """Unwrap a concrete bitvector expression into bytes."""
    return unwrap(value, msg).to_bytes(value.size() // 8, "big")


def zeval(
    model: z3.ModelRef, value: z3.BitVecRef, model_completion: bool = False
) -> z3.BitVecRef:
    """Evaluate a given bitvector expression with the given model."""
    if not z3.is_bv(value):
        raise ValueError("unexpected non-bitvector")
    return cast(z3.BitVecRef, model.eval(value, model_completion))


def zif(condition: Constraint, then: z3.BitVecRef, else_: z3.BitVecRef) -> z3.BitVecRef:
    """Return a symbolic if statement over bitvectors."""
    return cast(z3.BitVecRef, z3.If(condition, then, else_))


def zconcat(*values: z3.BitVecRef) -> z3.BitVecRef:
    """Return the concatenation of symbolic bitvectors."""
    # TODO: support zero-length bitvectors, empty hash, etc.
    return cast(z3.BitVecRef, z3.Concat(*values))


def zextract(high: int, low: int, value: z3.BitVecRef) -> z3.BitVecRef:
    """Return the result of slicing a symbolic bitvector."""
    return cast(z3.BitVecRef, z3.Extract(high, low, value))


def zand(*constraints: Constraint) -> z3.BoolRef:
    """Return the union of the given symbolic constraints."""
    return cast(z3.BoolRef, z3.And(*constraints))


def zget(dict: Dict[K, z3.BitVecRef], key: K, default: z3.BitVecRef) -> z3.BitVecRef:
    """Look up a key in a dictionary with a default value."""
    return dict.get(key, default)


def describe(value: z3.BitVecRef) -> str:
    """
    Produce a human-readable description of the given bitvector.

    For concrete bitvectors, returns a result in hexadecimal. Long values are
    broken into 256-bit chunks using dot syntax, e.g. "0x[1234.1]".

    For symbolic bitvectors, returns a hash based on the input variables.
    """
    value = simplify(value)
    if is_concrete(value):
        v: int = unwrap(value)
        if v < (1 << 256):
            return hex(v)
        p = []
        while v > 0:
            b = v & ((1 << 256) - 1)
            p.append(hex(b)[2:])
            v >>= 256
        return f"0x[{'.'.join(reversed(p))}]"
    else:
        digest = keccak.new(data=str(value).encode(), digest_bits=256).digest()
        return "#" + digest[:3].hex()


class Bytes:
    """A symbolic-length sequence of symbolic bytes. Immutable."""

    def __init__(self, length: uint256, array: z3.ArrayRef) -> None:
        """Create a new Bytes. For internal use."""
        self.length = length
        self.array = array

    @classmethod
    def concrete(cls, data: bytes | List[uint8]) -> Bytes:
        """Create a new Bytes from a concrete list of bytes."""
        length = BW(len(data))
        array = z3.K(z3.BitVecSort(256), BY(0))
        for i, b in enumerate(data):
            if z3.is_bv(b):
                assert cast(z3.BitVecRef, b).size() == 8
            array = cast(z3.ArrayRef, z3.Store(array, i, b))
        return Bytes(length, array)

    @classmethod
    def symbolic(cls, name: str) -> Bytes:
        """Create a new, fully-symbolic Bytes."""
        return Bytes(
            z3.BitVec(f"{name}.length", 256),
            z3.Array(name, z3.BitVecSort(256), z3.BitVecSort(8)),
        )

    def __getitem__(self, i: uint256) -> uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        assert i.size() == 256
        return cast(uint8, z3.If(i >= self.length, BY(0), self.array[i]))

    def require_concrete(self) -> bytes:
        """Unwrap this concrete-valued instance to bytes."""
        return bytes(unwrap(self[BW(i)]) for i in range(unwrap(self.length)))

    def evaluate(self, model: z3.ModelRef, model_completion: bool = False) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = unwrap(zeval(model, self.length, True))
        result = ""
        for i in range(length):
            b = zeval(model, self[BW(i)], model_completion)
            result += unwrap_bytes(b).hex() if is_concrete(b) else "??"
        return result


class Array:
    """
    A symbolic array. Mutable.

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

    def peek(self, key: z3.BitVecRef) -> z3.BitVecRef:
        """Look up the given symbolic key, but don't track the lookup."""
        return cast(z3.BitVecRef, self.array[key])

    def printable_diff(
        self, name: str, model: z3.ModelRef, original: Array
    ) -> Iterable[str]:
        """
        Evaluate a diff of this array against another.

        Yields a human-readable description of the differences.
        """
        diffs = [
            ("R", [(key, original.peek(key), None) for key in self.accessed]),
            ("W", [(key, self.peek(key), original.peek(key)) for key in self.written]),
        ]
        line = name

        for prefix, rows in diffs:
            concrete = {}
            for key, value, prior in rows:
                k = describe(zeval(model, key, True))
                v = describe(zeval(model, value, True))
                p = describe(zeval(model, prior, True)) if prior is not None else None
                concrete[k] = (v, p)

            for key in sorted(concrete.keys()):
                line += f"\t{prefix}: {key} "
                if len(key) > 34:
                    yield line
                    line = "\t"
                value, prior = concrete[key]
                line += f"-> {value}"
                if prior is not None:
                    if len(value) > 34:
                        yield line
                        line = "\t  "
                    line += " (no change)" if value == prior else f" (from {prior})"
                yield line
                line = ""

        if line == "":
            yield ""


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
        # Sometimes the solver return "unsat" but can't produce an unsatisfiable
        # core. Origintally I thought it was returning "unsat" incorrectly, but
        # that might not be true. This *can* happen if we add unnamed
        # constraints with `solver.add()` -- use `assert_and_track()` instead!
        assert len(solver.unsat_core()) > 0
        return False
    else:
        raise Exception(f"z3 failure: {solver.reason_unknown()}")
