"""Types for representing symbolic sequence of bytes."""

from __future__ import annotations

import abc
import copy
from typing import Any, Type, TypeVar

from smt import Constraint, Solver, Uint, Uint8, Uint256, concat_bytes, zArray

T = TypeVar("T", bound="Bytes")

BytesWrite = tuple[Uint256, "Uint8 | ByteSlice"]


class Bytes(abc.ABC):
    """A symbolic-length sequence of symbolic bytes."""

    def __init__(self, length: Uint256, array: zArray[Uint256, Uint8]) -> None:
        """Create a new Bytes. For internal use."""
        self.length = length
        self.array = array
        self.writes = list[BytesWrite]()  # writes to apply *on top of* array

    @classmethod
    def concrete(cls: Type[T], data: bytes | list[Uint8] = b"") -> T:
        """Create a new Bytes from a concrete list of bytes."""
        length = Uint256(len(data))
        array = zArray[Uint256, Uint8](Uint8(0))
        for i, b in enumerate(data):
            if isinstance(b, Uint):
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
            zArray[Uint256, Uint8](name),
        )

    @classmethod
    def conditional(cls: Type[T], name: str, constraint: Constraint) -> T:
        """
        Create a new, fully-symbolic Bytes.

        If the constraint is True, the Bytes is empty.
        """
        return cls(
            constraint.ite(Uint256(0), Uint256(f"{name}-LEN")),
            zArray[Uint256, Uint8](name),
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

    def bigvector(self, expected_length: int) -> Uint[Any]:
        """Return a single, large bitvector of this instance's bytes."""
        if (v := self.length.reveal()) is not None:
            assert expected_length == v
        return concat_bytes(*(self[Uint256(i)] for i in range(expected_length)))

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        if (length := self.length.reveal()) is None:
            return None
        data = list[int]()
        for i in range(length):
            if (v := self[Uint256(i)].reveal()) is None:
                return None
            data.append(v)
        return bytes(data)

    def describe(self, solver: Solver) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = solver.evaluate(self.length)
        result = ""
        for i in range(length):
            if i > 256:
                result += "..."
                break
            b = solver.evaluate(self[Uint256(i)])
            result += b.to_bytes(1).hex()
        return result

    def evaluate(self, solver: Solver) -> bytes:
        """Use a model to evaluate this instance as bytes."""
        length = solver.evaluate(self.length)
        if length > 256:
            raise ValueError("length too long to evaluate!")
        result = b""
        for i in range(length):
            result += solver.evaluate(self[Uint256(i)]).to_bytes(1)
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

    __hash__ = None  # type: ignore

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.array[i]
        for k, v in self.writes:
            if isinstance(v, ByteSlice):
                destOffset = k
                item = ((i >= destOffset) & (i < destOffset + v.length)).ite(
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
        if slice.length.reveal() == 0:
            # Short circuit e.g. in DELEGATECALL when retSize is zero.
            return

        self.length = (at + slice.length - Uint256(1) < self.length).ite(
            self.length,
            at + slice.length,
        )

        if len(self.writes) == 0 and (length := slice.length.reveal()) is not None:
            # Avoid creating custom writes when possible because of the
            # performance cliff (see above).
            for i in range(length):
                self[at + Uint256(i)] = slice[Uint256(i)]
        else:
            self.writes.append((at, slice))
