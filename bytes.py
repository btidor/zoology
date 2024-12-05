"""Types for representing symbolic sequences of bytes."""

from __future__ import annotations

import abc
import copy
from bisect import bisect
from dataclasses import dataclass, field
from typing import Any, Iterable, Self

from smt import (
    Addend,
    Array,
    Constraint,
    Solver,
    Uint,
    Uint8,
    Uint64,
    Uint256,
    compact_helper,
    concat_bytes,
    explode_bytes,
)

DESCRIBE_LIMIT = 256

BYTES = [Uint8(i) for i in range(256)]
INTEGERS = list[Uint256]()


class Bytes:
    """An immutable, symbolic-length sequence of symbolic bytes."""

    __slots__ = ("data", "length", "check_length", "array")

    def __init__(self, data: bytes | list[Uint8] = b"") -> None:
        """Create a new Bytes from concrete data."""
        self.data = data if isinstance(data, bytes) else None
        self.length = Uint256(len(data))
        self.check_length = False
        self.array = Array[Uint256, Uint8](BYTES[0])
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
        result = cls.__new__(cls)
        result.data = None
        # ASSUMPTION: call data and return data are no longer than 2^64 bytes.
        # CALL, RETURN, etc. incur gas costs for memory expansion, so this
        # should be a reasonable upper limit.
        result.length = Uint64(length if length is not None else f"{name}.length").into(
            Uint256
        )
        result.check_length = True
        result.array = Array[Uint256, Uint8](name)
        return result

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def __getitem__(self, i: Uint256) -> Uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        if self.check_length:
            return (i < self.length).ite(self.array[i], BYTES[0])
        return self.array[i]

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def bigvector(self) -> Uint[Any]:
        """Return a single, large bitvector of this instance's bytes."""
        if (n := self.length.reveal()) is None:
            raise ValueError("bigvector requires concrete length")
        return concat_bytes(*(self[Uint256(i)] for i in range(n)))

    def compact(self, solver: Solver, constraint: Constraint) -> Constraint:
        """Simplify using the given solver's contraints (a no-op)."""
        return constraint

    def describe(self, solver: Solver, prefix: int = 4) -> Iterable[str]:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = solver.evaluate(self.length)
        if length > DESCRIBE_LIMIT:
            yield from self.slice(Uint256(0), Uint256(DESCRIBE_LIMIT)).describe(
                solver, prefix=prefix
            )
            yield "..."
        elif length == 0:
            yield "-       "
        else:
            for i in range(length):
                if prefix and i == prefix:
                    yield " "
                yield solver.evaluate(self[Uint256(i)]).to_bytes(1).hex()

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
        elif (length := self.length.reveal()) is None:
            return None
        data = list[int]()
        for i in range(length):
            if (v := self[Uint256(i)].reveal()) is None:
                return None
            data.append(v)
        return bytes(data)


class ByteSlice(Bytes):
    """Represents an immutable slice of Bytes or Memory."""

    __slots__ = ("inner", "offset")

    def __init__(self, inner: Bytes | Memory, offset: Uint256, size: Uint256) -> None:
        """Create a new ByteSlice."""
        self.inner = copy.deepcopy(inner)
        self.offset = offset
        self.length = size
        self.data = None

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.inner[self.offset + i]
        return (i < self.length).ite(item, BYTES[0])

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
    __slots__ = ("writes",)

    def __init__(self, data: bytes = b"") -> None:
        """Create a new Memory with the given data."""
        self.writes = list[Write]()
        if data:
            self.writes.append(
                SliceWrite(
                    Addend(0),
                    ByteSlice(Bytes(data), Uint256(0), Uint256(len(data))),
                ),
            )

    def __getitem__(self, i: Uint256) -> Uint8:
        a = Addend.from_symbolic(i)
        k = bisect(self.writes, a, key=lambda w: w.offset) - 1
        write = self.writes[k]
        offset = a - write.offset
        assert (r := offset.reveal()) is not None
        match write:
            case ArrayWrite() as write:
                return write.array[Uint256(r)]
            case SliceWrite() as write:
                return write.slice[Uint256(r)]

    def __setitem__(self, i: Uint256, v: Uint8) -> None:
        a = Addend.from_symbolic(i)
        k = bisect(self.writes, a, key=lambda w: w.offset) - 1
        if k == -1:
            assert not self.writes
            self.writes.append(ArrayWrite(Addend(0)))
            k = 0
        match self.writes[k]:
            case ArrayWrite() as write:
                offset = a - write.offset
                assert (r := offset.reveal()) is not None
                write.array[Uint256(r)] = v
                if write.length < r:
                    write.length = r
            case SliceWrite() as write:
                raise NotImplementedError("__setitem__ cannot write to slice")

    def setword(self, i: Uint256, v: Uint256) -> None:
        """Write an entire Uint256 to memory starting at the given index."""
        for k, byte in enumerate(reversed(explode_bytes(v))):
            n = i + Uint256(k)
            self[n] = byte

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        # TODO: filter out nonoverlapping writes
        return ByteSlice(self, offset, size)

    def graft(self, slice: ByteSlice, at: Uint256) -> None:
        """Graft in a Bytes at the given offset."""
        offset = Addend.from_symbolic(at)
        if offset < self._length():
            if offset == Addend(0) and self._length() < Addend.from_symbolic(
                slice.length
            ):
                self.writes.clear()
            else:
                raise NotImplementedError("graft only supported at end of memory")
        elif (
            self.writes
            and isinstance(self.writes[-1], ArrayWrite)
            and self.writes[-1].length == 0
        ):
            self.writes.pop()
        self.writes.append(SliceWrite(offset, slice))

        next = offset + Addend.from_symbolic(slice.length)
        self.writes.append(ArrayWrite(next))

    def compact(self, solver: Solver, constraint: Constraint) -> Constraint:
        """Simplify array keys using the given solver's contraints."""
        return constraint

    def _length(self) -> Addend:
        if not self.writes:
            return Addend(0)
        match self.writes[-1]:
            case ArrayWrite() as last:
                return last.offset + Addend(last.length)
            case SliceWrite() as last:
                return last.offset + Addend.from_symbolic(last.slice.length)

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        data = list[int]()
        for write in self.writes:
            match write:
                case ArrayWrite():
                    n = write.length
                    source = write.array
                case SliceWrite():
                    if (n := write.slice.length.reveal()) is None:
                        return None
                    source = write.slice
            for i in range(n):
                if (v := source[Uint256(i)].reveal()) is None:
                    return None
                data.append(v)
        return bytes(data)


@dataclass(slots=True)
class ArrayWrite(abc.ABC):
    """TODO."""

    offset: Addend
    length: int = field(default=0)
    array: Array[Uint256, Uint8] = field(
        default_factory=lambda: Array[Uint256, Uint8](Uint8(0))
    )


@dataclass(frozen=True, slots=True)
class SliceWrite(abc.ABC):
    """TODO."""

    offset: Addend
    slice: ByteSlice


type Write = ArrayWrite | SliceWrite
