"""Types for representing array-like symbolic state."""

from __future__ import annotations

import abc
import copy
from typing import (
    Callable,
    Dict,
    Generic,
    Iterable,
    List,
    Optional,
    Tuple,
    Type,
    TypeAlias,
    TypeGuard,
    TypeVar,
    Union,
)

from pysmt.fnode import FNode
from pysmt.shortcuts import BVConcat, Function, Symbol
from pysmt.typing import FunctionType

from smt import BitVector, Constraint, Uint8, Uint256
from solver import Solver

K = TypeVar("K", bound=BitVector)
V = TypeVar("V", bound=BitVector)

T = TypeVar("T", bound="Bytes")
U = TypeVar("U")


class Array(Generic[K, V]):
    """
    A symbolic array. Mutable.

    Tracks which keys are accessed and written.
    """

    def __init__(self, default: Callable[[K], V]) -> None:
        """Create a new Array. For internal use."""
        self.default = default
        self.writes: List[Tuple[K, V]] = []
        self.accessed: List[K] = []
        self.written: List[K] = []

    @classmethod
    def concrete(cls, key: Type[K], val: V) -> Array[K, V]:
        """Create a new Array with a concrete default value."""
        return Array(lambda k: val)

    @classmethod
    def symbolic(cls, name: str, key: Type[K], val: Type[V]) -> Array[K, V]:
        """Create a new Array as an uninterpreted function."""
        array = Symbol(name, FunctionType(val._pysmt_type(), [key._pysmt_type()]))
        return Array(lambda k: val(Function(array, [k.node])))

    def __getitem__(self, key: K) -> V:
        """Look up the given symbolic key."""
        self.accessed.append(key)
        return self.peek(key)

    def __setitem__(self, key: K, val: V) -> None:
        """Set the given symbolic key to the given symbolic value."""
        self.written.append(key)
        self.writes.append((key, val))

    def peek(self, key: K) -> V:
        """Look up the given symbolic key, but don't track the lookup."""
        r = self.default(key)
        for k, v in self.writes:
            r = (k == key).ite(v, r)
        return r

    def poke(self, key: K, val: V) -> None:
        """Set up the given symbolic key, but don't track the write."""
        self.writes.append((key, val))

    def printable_diff(
        self, name: str, solver: Solver, original: Array[K, V]
    ) -> Iterable[str]:
        """
        Evaluate a diff of this array against another.

        Yields a human-readable description of the differences.
        """
        diffs: List[Tuple[str, List[Tuple[K, V, Optional[V]]]]] = [
            ("R", [(key, original.peek(key), None) for key in self.accessed]),
            (
                "W",
                [(key, self.peek(key), original.peek(key)) for key, _ in self.writes],
            ),
        ]
        line = name

        for prefix, rows in diffs:
            concrete: Dict[str, Tuple[str, Optional[str]]] = {}
            for key, value, prior in rows:
                k = solver.evaluate(key, True).describe()
                v = solver.evaluate(value, True).describe()
                p = (
                    solver.evaluate(prior, True).describe()
                    if prior is not None
                    else None
                )
                if v != p:
                    concrete[k] = (v, p)

            for k in sorted(concrete.keys()):
                line += f"\t{prefix}: {k} "
                if len(k) > 34:
                    yield line
                    line = "\t"
                v, p = concrete[k]
                line += f"-> {v}"
                if p is not None:
                    if len(v) > 34:
                        yield line
                        line = "\t  "
                    line += f" (from {p})"
                yield line
                line = ""

        if line == "":
            yield ""


BytesWrite: TypeAlias = Union[
    Tuple[Uint256, Uint8],
    Tuple[Uint256, "ByteSlice"],
]


def present(values: List[Optional[U]]) -> TypeGuard[List[U]]:
    """Return true iff the given list has no Nones."""
    return all(v is not None for v in values)


class Bytes(abc.ABC):
    """A symbolic-length sequence of symbolic bytes."""

    def __init__(self, length: Uint256, array: Array[Uint256, Uint8]) -> None:
        """Create a new Bytes. For internal use."""
        self.length = length
        self.array = array
        self.writes: List[BytesWrite] = []  # writes to apply *on top of* array

    @classmethod
    def concrete(cls: Type[T], data: bytes | List[Uint8]) -> T:
        """Create a new Bytes from a concrete list of bytes."""
        length = Uint256(len(data))
        array = Array.concrete(Uint256, Uint8(0))
        for i, b in enumerate(data):
            if isinstance(b, Uint8):
                array[Uint256(i)] = b
            else:
                assert isinstance(b, int)
                array[Uint256(i)] = Uint8(b)
        return cls(length, array)

    @classmethod
    def symbolic(cls: Type[T], name: str, length: Optional[int] = None) -> T:
        """Create a new, fully-symbolic Bytes."""
        return cls(
            Uint256(length if length is not None else f"{name}.length"),
            Array.symbolic(name, Uint256, Uint8),
        )

    @classmethod
    def conditional(cls: Type[T], name: str, constraint: Constraint) -> T:
        """
        Create a new, fully-symbolic Bytes.

        If the constraint is True, the Bytes is empty.
        """
        return cls(
            constraint.ite(Uint256(0), Uint256(f"{name}.length")),
            Array.symbolic(name, Uint256, Uint8),
        )

    @abc.abstractmethod
    def __getitem__(self, i: Uint256) -> Uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        ...

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def _bigvector(self) -> FNode:
        """
        Return a single, large bitvector of this instance's bytes.

        Requires a concrete length.
        """
        return BVConcat(*[self[Uint256(i)].node for i in range(self.length.unwrap())])

    def maybe_unwrap(self) -> Optional[bytes]:
        """Unwrap this instance to bytes."""
        if (length := self.length.maybe_unwrap()) is None:
            return None
        data = [self[Uint256(i)].maybe_unwrap() for i in range(length)]
        if not present(data):
            return None
        return bytes(data)

    def unwrap(self) -> bytes:
        """
        Unwrap this instance to bytes.

        Requires a concrete length and all-concrete values.
        """
        if (data := self.maybe_unwrap()) is None:
            raise ValueError("unexpected symbolic length or data")
        return data

    def evaluate(self, solver: Solver, model_completion: bool = False) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = solver.evaluate(self.length, True).unwrap()
        result = ""
        for i in range(length):
            b = solver.evaluate(self[Uint256(i)], model_completion)
            result += b.unwrap(bytes).hex() if b is not None else "??"
        return result


class FrozenBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Immutable."""

    def __getitem__(self, i: Uint256) -> Uint8:
        return self.array[i]


class ByteSlice(FrozenBytes):
    """A symbolic-length slice of symbolic bytes. Immutable."""

    def __init__(self, inner: Bytes, offset: Uint256, size: Uint256) -> None:
        """Create a new ByteSlice."""
        self.inner = copy.deepcopy(inner)
        self.offset = offset
        self.length = size

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.inner[self.offset + i]
        return (i < self.length).ite(item, Uint8(0))


class MutableBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Mutable."""

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.array[i]
        for k, v in self.writes:
            if isinstance(v, ByteSlice):
                destOffset = k
                item = Constraint.all(i >= destOffset, i < destOffset + v.length).ite(
                    v[i - destOffset],
                    item,
                )
            else:
                item = (i == k).ite(v, item)
        return (i < self.length).ite(item, Uint8(0))

    def __setitem__(self, i: Uint256, v: Uint8) -> None:
        self.length = (i < self.length).ite(self.length, i + Uint256(1))
        if len(self.writes) == 0:
            # Warning: passing writes through to the underlying array when there
            # are no custom writes is a good optimization (~12% speedup), but it
            # does create a performance cliff.
            self.array[i] = v
        else:
            self.writes.append((i, v))

    def graft(self, slice: ByteSlice, at: Uint256) -> None:
        """Graft another Bytes into this one at the given offset."""
        if slice.length.maybe_unwrap() == 0:
            # Short circuit e.g. in DELEGATECALL when retSize is zero.
            return

        self.length = (at + slice.length - Uint256(1) < self.length).ite(
            self.length,
            at + slice.length,
        )

        if (
            len(self.writes) == 0
            and (length := slice.length.maybe_unwrap()) is not None
        ):
            # Avoid creating custom writes when possible because of the
            # performance cliff (see above).
            for i in range(length):
                self[at + Uint256(i)] = slice[Uint256(i)]
        else:
            self.writes.append((at, slice))
