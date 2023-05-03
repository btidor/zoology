"""Types for representing symbolic sequence of bytes."""

from __future__ import annotations

import abc
import copy
from typing import Type, TypeGuard, TypeVar

from pybitwuzla import BitwuzlaTerm, Kind

from smt.arrays import Array
from smt.bitwuzla import mk_term
from smt.smt import Constraint, Uint8, Uint256
from smt.solver import Solver

T = TypeVar("T", bound="Bytes")

BytesWrite = tuple[Uint256, "Uint8 | ByteSlice"]


def present(values: list[int | None]) -> TypeGuard[list[int]]:
    """Return true iff the given list has no Nones."""
    return all(v is not None for v in values)


class Bytes(abc.ABC):
    """A symbolic-length sequence of symbolic bytes."""

    def __init__(self, length: Uint256, array: Array[Uint256, Uint8]) -> None:
        """Create a new Bytes. For internal use."""
        self.length = length
        self.array = array
        self.writes: list[BytesWrite] = []  # writes to apply *on top of* array

    @classmethod
    def concrete(cls: Type[T], data: bytes | list[Uint8]) -> T:
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
    def symbolic(cls: Type[T], name: str, length: int | None = None) -> T:
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

    def _bigvector(self, expected_length: int) -> BitwuzlaTerm:
        """Return a single, large bitvector of this instance's bytes."""
        length = self.length.maybe_unwrap() or expected_length
        assert length == expected_length
        result = mk_term(Kind.BV_CONCAT, [self[Uint256(i)].node for i in range(length)])
        assert isinstance(result, BitwuzlaTerm)
        return result

    def maybe_unwrap(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        if (length := self.length.maybe_unwrap()) is None:
            return None
        data = [self[Uint256(i)].maybe_unwrap() for i in range(length)]
        if not present(data):
            return None
        return bytes(data)

    def unwrap(self, msg: str = "unexpected symbolic value") -> bytes:
        """
        Unwrap this instance to bytes.

        Requires a concrete length and all-concrete values.
        """
        if (data := self.maybe_unwrap()) is None:
            raise ValueError(msg)
        return data

    def describe(self, solver: Solver) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = solver.evaluate(self.length).unwrap()
        result = ""
        for i in range(length):
            if i > 256:
                result += "..."
                break
            b = solver.evaluate(self[Uint256(i)])
            result += b.unwrap(bytes).hex()
        return result

    def evaluate(self, solver: Solver) -> bytes:
        """Use a model to evaluate this instance as bytes."""
        length = solver.evaluate(self.length).unwrap()
        if length > 256:
            raise ValueError("length too long to evaluate!")
        result = b""
        for i in range(length):
            result += solver.evaluate(self[Uint256(i)]).unwrap(bytes)
        return result


class FrozenBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Immutable."""

    def __getitem__(self, i: Uint256) -> Uint8:
        return (i < self.length).ite(self.array[i], Uint8(0))


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
