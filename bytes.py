"""Types for representing symbolic sequence of bytes."""

from __future__ import annotations

import copy
from typing import Any, Self, TypeVar

from smt import (
    Constraint,
    Solver,
    Uint,
    Uint8,
    Uint256,
    compact_helper,
    compact_zarray,
    concat_bytes,
    zArray,
)

T = TypeVar("T", bound="Bytes")

BytesWrite = tuple[Uint256, "Uint8 | ByteSlice"]

DESCRIBE_LIMIT = 256

BYTES = [Uint8(i) for i in range(256)]
INTEGERS = list[Uint256]()


class Bytes:
    """An immutable, symbolic-length sequence of symbolic bytes."""

    def __init__(self, data: bytes | list[Uint8] = b"") -> None:
        """Create a new Bytes from concrete data."""
        self.data = data if isinstance(data, bytes) else None
        self.length = Uint256(len(data))
        self.array = zArray[Uint256, Uint8](Uint8(0))
        if isinstance(data, bytes):
            for i in range(len(INTEGERS), len(data)):
                INTEGERS.append(Uint256(i))
            for i, b in enumerate(data):
                self.array[INTEGERS[i]] = BYTES[b]
        else:
            for i, b in enumerate(data):
                self.array[Uint256(i)] = b

    @classmethod
    def fromhex(cls, str: str) -> Bytes:
        """Create a new Bytes from a concrete hexadecimal string."""
        return cls(bytes.fromhex(str))

    @classmethod
    def symbolic(cls, name: str, length: int | None = None) -> Bytes:
        """Create a new, fully-symbolic Bytes."""
        return cls.custom(
            Uint256(length if length is not None else f"{name}.length"),
            zArray[Uint256, Uint8](name),
        )

    @classmethod
    def custom(cls, length: Uint256, array: zArray[Uint256, Uint8]) -> Bytes:
        """Create a new Bytes with custom properties."""
        result = cls.__new__(cls)
        result.data, result.length, result.array = None, length, array
        return result

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def __getitem__(self, i: Uint256) -> Uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        return (i < self.length).ite(self.array[i], Uint8(0))

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def bigvector(self, expected_length: int) -> Uint[Any]:
        """Return a single, large bitvector of this instance's bytes."""
        if (v := self.length.reveal()) is not None:
            assert expected_length == v
        return concat_bytes(*(self[Uint256(i)] for i in range(expected_length)))

    def compact(self, solver: Solver, constraint: Constraint) -> Constraint:
        """Simplify using the given solver's contraints (a no-op)."""
        return constraint

    def describe(self, solver: Solver) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        try:
            return self.evaluate(solver).hex()
        except ValueError:
            return (
                self.slice(Uint256(0), Uint256(DESCRIBE_LIMIT)).describe(solver) + "..."
            )

    def evaluate(self, solver: Solver) -> bytes:
        """Use a model to evaluate this instance as bytes."""
        length = solver.evaluate(self.length)
        if length > DESCRIBE_LIMIT:
            raise ValueError("length too long to evaluate!")
        result = b""
        for i in range(length):
            result += solver.evaluate(self[Uint256(i)]).to_bytes(1)
        return result

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        if self.data is not None:
            return self.data
        return _reveal(self)


class ByteSlice(Bytes):
    """Represents an immutable slice of Bytes or Memory."""

    def __init__(self, inner: Bytes | Memory, offset: Uint256, size: Uint256) -> None:
        """Create a new ByteSlice."""
        self.inner = copy.deepcopy(inner)
        self.offset = offset
        self.length = size
        self.data = None

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.inner[self.offset + i]
        return (i < self.length).ite(item, Uint8(0))

    def compact(self, solver: Solver, constraint: Constraint) -> Constraint:
        """Simplify length and offset using the given solver's contraints."""
        length_, offset_ = solver.evaluate(self.length), solver.evaluate(self.offset)

        constraint = self.inner.compact(solver, constraint)
        constraint, self.length = compact_helper(
            solver, constraint, self.length, Uint256(length_)
        )
        constraint, self.offset = compact_helper(
            solver, constraint, self.offset, Uint256(offset_)
        )
        return constraint


class Memory:
    """A mutable, symbolic-length sequence of symbolic bytes."""

    __hash__ = None  # type: ignore

    def __init__(self, data: bytes = b"") -> None:
        """Create a new, empty Memory."""
        self.length = Uint256(0)
        self.array = zArray[Uint256, Uint8](Uint8(0))
        self.writes = list[BytesWrite]()  # writes to apply *on top of* array
        for i, b in enumerate(data):
            self[Uint256(i)] = Uint8(b)

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

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def graft(self, slice: ByteSlice, at: Uint256) -> None:
        """Graft in a Bytes at the given offset."""
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

    def compact(self, solver: Solver, constraint: Constraint) -> Constraint:
        """Simplify array keys using the given solver's contraints."""
        length_ = Uint256(solver.evaluate(self.length))
        for k, v in self.writes:
            if isinstance(v, ByteSlice):
                constraint &= v.compact(solver, constraint)
        constraint, self.length = compact_helper(
            solver, constraint, self.length, length_
        )

        # Try passing through writes to the underlying array again, now that
        # we've simplified the slice lengths:
        while self.writes:
            k, v = self.writes[0]
            if isinstance(v, ByteSlice):
                if (n := v.length.reveal()) is None:
                    break
                for i in range(n):
                    self.array[k + Uint256(i)] = v[Uint256(i)]
            else:
                self.array[k] = v
            self.writes.pop(0)

        assert solver.check()
        return compact_zarray(solver, constraint, self.array)

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        return _reveal(self)


def _reveal(instance: Bytes | Memory) -> bytes | None:
    if (length := instance.length.reveal()) is None:
        return None
    data = list[int]()
    for i in range(length):
        if (v := instance[Uint256(i)].reveal()) is None:
            return None
        data.append(v)
    return bytes(data)
