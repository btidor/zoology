"""Types for representing symbolic sequences of bytes."""

from __future__ import annotations

import abc
import copy
from dataclasses import dataclass, field
from typing import Any, Iterable, Never, Self

from smt import (
    Addend,
    Array,
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

    def get(self, i: Uint256, solver: Solver) -> Uint8:
        """TODO."""
        return self[i]

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def bigvector(self) -> Uint[Any]:
        """Return a single, large bitvector of this instance's bytes."""
        if (n := self.length.reveal()) is None:
            raise ValueError("bigvector requires concrete length")
        return concat_bytes(*(self.get(Uint256(i), None) for i in range(n)))

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

    def reveal(self, solver: Solver) -> bytes | None:
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

    def __getitem__(self, i: Uint256) -> Never:
        raise NotImplementedError

    def get(self, i: Uint256, solver: Solver) -> Uint8:
        """TODO."""
        match self.inner:
            case Memory() | ByteSlice():
                item = self.inner.get(self.offset + i, solver)
            case Bytes():
                item = self.inner[self.offset + i]
        return (i < self.length).ite(item, BYTES[0])

    def reveal(self, solver: Solver) -> bytes | None:
        """Unwrap this instance to bytes."""
        if (length := self.length.reveal()) is None:
            return None
        data = list[int]()
        for i in range(length):
            if (v := self.get(Uint256(i), solver).reveal()) is None:
                return None
            data.append(v)
        return bytes(data)


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
                    Addend(len(data)),
                    ByteSlice(Bytes(data), Uint256(0), Uint256(len(data))),
                ),
            )

    def get(self, i: Uint256, solver: Solver) -> Uint8:
        """TODO."""
        a = Addend.from_symbolic(i, solver)
        for write in reversed(self.writes):
            match write:
                case SetWrite():
                    if a in write.data:
                        return write.data[a]
                case SliceWrite():
                    if a >= write.start and a < write.stop:
                        offset = a - write.start
                        assert (
                            r := offset.reveal()
                        ) is not None, "TODO: symbolic slice offset"
                        return write.data.get(Uint256(r), solver)
        # TODO: how to handle unknown terms in Addend which may be zero, etc.?
        return BYTES[0]

    def setbyte(self, i: Uint256, v: Uint8, solver: Solver) -> None:
        """TODO."""
        a = Addend.from_symbolic(i, solver)
        if self.writes and isinstance(self.writes[-1], SetWrite):
            write = self.writes[-1]
        else:
            write = SetWrite()
            self.writes.append(write)
        write.data[a] = v

    def setword(self, i: Uint256, v: Uint256, solver: Solver) -> None:
        """Write an entire Uint256 to memory starting at the given index."""
        for k, byte in enumerate(reversed(explode_bytes(v))):
            n = i + Uint256(k)
            self.setbyte(n, byte, solver)

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        # TODO: filter out nonoverlapping writes
        return ByteSlice(self, offset, size)

    def graft(self, slice: ByteSlice, at: Uint256, solver: Solver) -> None:
        """Graft in a Bytes at the given offset."""
        a = Addend.from_symbolic(at, solver)
        self.writes.append(
            SliceWrite(a, a + Addend.from_symbolic(slice.length, solver), slice)
        )

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        data = list[int]()
        for write in self.writes:
            match write:
                case SetWrite():
                    raise NotImplementedError()
                case SliceWrite():
                    if (n := write.data.length.reveal()) is None:
                        return None
                    source = write.data
            for i in range(n):
                if (v := source[Uint256(i)].reveal()) is None:
                    return None
                data.append(v)
        return bytes(data)


@dataclass(slots=True)
class SetWrite(abc.ABC):
    """TODO."""

    data: dict[Addend, Uint8] = field(default_factory=dict)


@dataclass(frozen=True, slots=True)
class SliceWrite(abc.ABC):
    """TODO."""

    start: Addend
    stop: Addend
    data: ByteSlice

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self


type Write = SetWrite | SliceWrite
