"""Types for representing symbolic sequences of bytes."""

from __future__ import annotations

import abc
import copy
from dataclasses import dataclass, field
from typing import Any, Iterable, Self

from smt import (
    Array,
    BitwuzlaTerm,
    Offset,
    PartialOrderError,
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
    __slots__ = ("addends", "writes")

    def __init__(self, data: bytes = b"") -> None:
        """Create a new Memory with the given data."""
        # List of terms used in constructing offsets. During narrowing, we check
        # that every addend fits in a Uint64, guaranteeing that offset
        # arithmetic does not overflow.
        self.addends = set[BitwuzlaTerm]()  # TODO: check during narrowing
        self.writes = list[Write]()
        if data:
            self.writes.append(
                SliceWrite(
                    Offset(0),
                    Offset(len(data)),
                    ByteSlice(Bytes(data), Uint256(0), Uint256(len(data))),
                ),
            )

    def __deepcopy__(self, memo: Any) -> Self:
        result = copy.copy(self)
        result.addends = copy.copy(result.addends)
        result.writes = copy.copy(result.writes)
        return result

    def _make_offset(self, value: Uint256) -> Offset:
        return Offset.from_symbolic(value, self.addends)

    def __getitem__(self, i: Uint256) -> Uint8:
        a = self._make_offset(i)
        # print(f"__getitem__({i}) ~ {a}")
        item = BYTES[0]
        for write in self.writes:
            # print(f" try {write.start} {write.stop}")
            try:
                if a < write.start:
                    continue
                elif a >= write.stop:
                    continue
                item = write[a]
                # print(f" = {item}")
            except PartialOrderError:
                try:
                    cond = (i >= write.start.to_symbolic()) & (
                        i < write.stop.to_symbolic()
                    )
                    item = cond.ite(write[a], item)
                    # print(f" ite {write[a]} {item}")
                except AssertionError:
                    print("TODO")
                    print(a, write.start)
                    raise
        return item

    def __setitem__(self, i: Uint256, v: Uint8) -> None:
        a = self._make_offset(i)
        for write in reversed(self.writes):
            try:
                if a < write.start:
                    continue
                elif a > write.stop:
                    continue
                match write:
                    case ArrayWrite():
                        write[a] = v
                        return
                    case SliceWrite():
                        if a == write.stop:
                            continue
                        break
            except PartialOrderError:
                break

        write = ArrayWrite(a, a + Offset(1))
        write[a] = v
        self.writes.append(write)

    def setword(self, i: Uint256, v: Uint256) -> None:
        """Write an entire Uint256 to memory starting at the given index."""
        for k, byte in enumerate(reversed(explode_bytes(v))):
            self[i + Uint256(k)] = byte

    def slice(self, offset: Uint256, size: Uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        # TODO: filter out nonoverlapping writes
        return ByteSlice(self, offset, size)

    def graft(self, slice: ByteSlice, at: Uint256) -> None:
        """Graft in a Bytes at the given offset."""
        a = self._make_offset(at)
        self.writes.append(SliceWrite(a, a + self._make_offset(slice.length), slice))

    def reveal(self) -> bytes | None:
        """Unwrap this instance to bytes."""
        data = list[int]()
        for write in self.writes:
            match write:
                case ArrayWrite():
                    raise NotImplementedError()
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

    start: Offset
    stop: Offset
    array: Array[Uint256, Uint8] = field(
        default_factory=lambda: Array[Uint256, Uint8](Uint8(0))
    )

    def __getitem__(self, abs: Offset) -> Uint8:
        return self.array[abs.safesub(self.start)]

    def __setitem__(self, abs: Offset, val: Uint8) -> None:
        if abs < self.stop:
            pass  # ok
        elif abs == self.stop:
            self.stop += Offset(1)
        else:
            raise NotImplementedError(
                f"discontinuous offset: create another ArrayWrite! {abs} {self.stop}"
            )
        self.array[abs.safesub(self.start)] = val


@dataclass(frozen=True, slots=True)
class SliceWrite(abc.ABC):
    """TODO."""

    start: Offset
    stop: Offset
    slice: ByteSlice

    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any) -> Self:
        return self

    def __getitem__(self, abs: Offset) -> Uint8:
        return self.slice[abs.safesub(self.start)]


type Write = ArrayWrite | SliceWrite
