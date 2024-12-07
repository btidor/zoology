"""Types for representing symbolic sequences of bytes."""

from __future__ import annotations

import copy
from dataclasses import dataclass
from typing import Any, Iterable, Self

from smt import (
    Array,
    Constraint,
    Offset,
    Solver,
    Uint,
    Uint8,
    Uint64,
    Uint256,
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
        match self.inner:
            case Memory() | ByteSlice():
                item = self.inner[self.offset + i]
            case Bytes():
                item = self.inner[self.offset + i]
        return (i < self.length).ite(item, BYTES[0])

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


class Memory:
    """A mutable, symbolic-length sequence of symbolic bytes."""

    __hash__ = None  # type: ignore
    __slots__ = ("base", "writes", "invalid")

    def __init__(self, data: bytes = b"") -> None:
        """Create a new Memory with the given data."""
        self.base = Array[Uint256, Uint8](Uint8(0))
        self.writes = list[Write]()
        self.invalid = Constraint(False)
        for i, b in enumerate(data):
            self[Uint256(i)] = Uint8(b)

    def __getitem__(self, i: Uint256) -> Uint8:
        try:
            offset = Offset(i)
            self.invalid |= offset.invalid()
        except AssertionError:
            result = self.base[i]
            for write in self.writes:
                match write:
                    case SliceWrite():
                        s0 = write.start.symbolic()
                        s1 = write.stop.symbolic()
                        result = ((i >= s0) & (i < s1)).ite(write.slice[i - s0], result)
                    case ByteWrite():
                        result = (i == write.offset.symbolic()).ite(write.byte, result)
            return result

        result = self.base[i]
        for write in reversed(self.writes):
            match write:
                case SliceWrite():
                    if offset < write.start:
                        continue
                    elif offset >= write.stop:
                        continue
                    elif offset >= write.start and offset < write.stop:
                        delta = offset.delta(write.start)
                        assert delta is not None
                        return write.slice[delta.symbolic()]
                    else:
                        break
                case ByteWrite():
                    if offset < write.offset:
                        continue
                    elif offset > write.offset:
                        continue
                    elif offset == write.offset:
                        return write.byte
                    else:
                        break
        for write in self.writes:
            match write:
                case SliceWrite():
                    if offset < write.start:
                        continue
                    elif offset >= write.stop:
                        continue
                    else:
                        s0 = write.start.symbolic()
                        s1 = write.stop.symbolic()
                        delta = offset.delta(write.start)
                        k = delta.symbolic() if delta else i - s0
                        result = ((i >= s0) & (i < s1)).ite(write.slice[k], result)
                case ByteWrite():
                    if offset < write.offset:
                        continue
                    elif offset > write.offset:
                        continue
                    else:
                        result = (offset.symbolic() == write.offset.symbolic()).ite(
                            write.byte, result
                        )
        return result

    def __setitem__(self, i: Uint256, v: Uint8) -> None:
        offset = Offset(i)
        self.invalid |= offset.invalid()
        for write in self.writes:
            match write:
                case SliceWrite():
                    if offset < write.start:
                        continue
                    elif offset >= write.stop:
                        continue
                case ByteWrite():
                    if offset < write.offset:
                        continue
                    elif offset > write.offset:
                        continue
            self.writes.append(ByteWrite(offset, v))
            return
        self.base[i] = v

    def setword(self, i: Uint256, v: Uint256) -> None:
        """Write an entire Uint256 to memory starting at the given index."""
        for k, byte in enumerate(reversed(explode_bytes(v))):
            self[i + Uint256(k)] = byte

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def graft(self, slice: ByteSlice, at: Uint256) -> None:
        """Graft in a Bytes at the given offset."""
        if (n := slice.length.reveal()) is not None:
            for i in range(n):
                self[at + Uint256(i)] = slice[Uint256(i)]
        else:
            start = Offset(at)
            stop = Offset(at + slice.length)
            self.writes.append(SliceWrite(start, stop, slice))

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        raise NotImplementedError("reveal")


@dataclass
class SliceWrite:
    """TODO."""

    start: Offset
    stop: Offset

    slice: ByteSlice


@dataclass
class ByteWrite:
    """TODO."""

    offset: Offset
    byte: Uint8


type Write = SliceWrite | ByteWrite
