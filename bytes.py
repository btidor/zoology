"""Types for representing symbolic sequence of bytes."""

from __future__ import annotations

import copy
from typing import Any, ClassVar, Iterable, Self

from smt import Array, Solver, Uint, Uint8, Uint64, Uint256

type BytesWrite = tuple[Uint256, Uint8 | ByteSlice]

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
        return Uint[8 * n].concat(*(self[Uint256(i)] for i in range(n)))

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
        return _reveal(self)


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

    def bigvector(self) -> Uint[Any]:
        """Return a single, large bitvector of this instance's bytes."""
        if (
            isinstance(self.inner, Memory)
            and (start := self.offset.reveal()) is not None
            and (size := self.length.reveal() is not None)
            and start % 0x20 == 0
            and size % 0x20 == 0
        ):
            words = list[Uint256]()
            for i in range(start, start + size, 0x20):
                if i in self.inner.wordcache:
                    words.append(self.inner.wordcache[i])
                else:
                    return super().bigvector()
            return Uint256.concat(*words)
        return super().bigvector()


class Memory:
    """A mutable, symbolic-length sequence of symbolic bytes."""

    __hash__: ClassVar[None] = None  # pyright: ignore[reportIncompatibleMethodOverride]
    __slots__ = ("length", "array", "writes", "wordcache")

    def __init__(self, data: bytes = b"") -> None:
        """Create a new, empty Memory."""
        self.length = Uint256(0)
        self.array = Array[Uint256, Uint8](BYTES[0])
        self.writes = list[BytesWrite]()  # writes to apply *on top of* array
        # When hashing mapping keys, Solidity programs put the values to be
        # hashed in the reserved range [0x0, 0x40). Splitting up the key into
        # bytes and reassembling it is slow, so we optimistically cache MSTOREd
        # words here.
        self.wordcache = dict[int, Uint256]()
        for i, b in enumerate(data):
            self[Uint256(i)] = BYTES[b]

    def __getitem__(self, i: Uint256) -> Uint8:
        item = self.array[i]
        for at, write in self.writes:
            match write:
                case ByteSlice():
                    # Compute the index relative to the grafted slice, assuming
                    # the index falls within this write.
                    delta = i - at

                    # ASSUMPTION: all memory indexes are small (below 2^64), so
                    # index math never underflows.
                    if (delta < Uint256(0)).reveal() is True:
                        continue

                    # Quickly check if the index falls outside this write, in
                    # the other direction.
                    #
                    # ASSUMPTION: all memory grafts are smaller than 2^64, so
                    # index math never underflows.
                    #
                    if (i - at >= write.length).reveal() is True:
                        continue

                    item = (delta < write.length).ite(write[delta], item)
                case Uint():
                    match (eq := i == at).reveal():
                        case True:
                            item = write
                        case False:
                            pass
                        case None:
                            item = eq.ite(write, item)
        return item

    def __setitem__(self, i: Uint256, v: Uint8) -> None:
        self.length = (i < self.length).ite(self.length, i + Uint256(1))
        self.wordcache.clear()
        if len(self.writes) == 0:
            # Warning: passing writes through to the underlying array when there
            # are no custom writes is a good optimization (~12% speedup), but it
            # does create a performance cliff.
            self.array[i] = v
        else:
            self.writes.append((i, v))

    def setword(self, i: Uint256, v: Uint256) -> None:
        """Write an entire Uint256 to memory starting at the given index."""
        self.length = (i + Uint256(0x20) <= self.length).ite(
            self.length, i + Uint256(0x20)
        )
        if (i_ := i.reveal()) is not None and i_ % 0x20 == 0:
            self.wordcache[i_] = v
        else:
            self.wordcache.clear()
        for k, byte in enumerate(reversed(Uint8.explode(v))):
            n = i + Uint256(k)
            if len(self.writes) == 0:
                self.array[n] = byte
            else:
                self.writes.append((n, byte))

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
        self.wordcache.clear()

        if len(self.writes) == 0 and (length := slice.length.reveal()) is not None:
            # Avoid creating custom writes when possible because of the
            # performance cliff (see above).
            for i in range(length):
                self[at + Uint256(i)] = slice[Uint256(i)]
        else:
            self.writes.append((at, slice))

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
