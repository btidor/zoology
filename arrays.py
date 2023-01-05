"""Types for representing array-like symbolic state."""

from __future__ import annotations

import abc
import copy
from typing import Any, Iterable, List, Tuple, TypeAlias, Union

import z3

from symbolic import (
    BW,
    BY,
    Model,
    describe,
    is_bitvector,
    is_concrete,
    simplify,
    uint8,
    uint256,
    unwrap,
    unwrap_bytes,
    zand,
    zconcat,
    zget,
    zif,
    zstore,
)


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
        return zget(self.array, key)

    def __setitem__(self, key: z3.BitVecRef, val: z3.BitVecRef) -> None:
        """Set the given symbolic key to the given symbolic value."""
        self.written.append(key)
        self.array = zstore(self.array, key, val)

    def peek(self, key: z3.BitVecRef) -> z3.BitVecRef:
        """Look up the given symbolic key, but don't track the lookup."""
        return zget(self.array, key)

    def printable_diff(self, name: str, model: Model, original: Array) -> Iterable[str]:
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
                k = describe(model.evaluate(key, True))
                v = describe(model.evaluate(value, True))
                p = describe(model.evaluate(prior, True)) if prior is not None else None
                if v != p:
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
                    line += f" (from {prior})"
                yield line
                line = ""

        if line == "":
            yield ""


BytesWrite: TypeAlias = Union[
    Tuple[uint256, uint8],
    Tuple[uint256, "ByteSlice"],
]


class Bytes(abc.ABC):
    """A symbolic-length sequence of symbolic bytes."""

    def __init__(self, length: uint256, array: z3.ArrayRef) -> None:
        """Create a new Bytes. For internal use."""
        assert length.size() == 256
        self.length = length

        domain, range = array.domain(), array.range()
        assert isinstance(domain, z3.BitVecSortRef)
        assert isinstance(range, z3.BitVecSortRef)
        assert domain.size() == 256
        assert range.size() == 8
        self.array = array

        self.writes: List[BytesWrite] = []  # writes to apply *on top of* array

    @classmethod
    def concrete(cls, data: bytes | List[uint8]) -> Any:  # TODO: switch to Self
        """Create a new Bytes from a concrete list of bytes."""
        length = BW(len(data))
        array = z3.K(z3.BitVecSort(256), BY(0))
        for i, b in enumerate(data):
            if is_bitvector(b):
                assert b.size() == 8
                array = zstore(array, BW(i), b)
            else:
                assert isinstance(b, int)
                array = zstore(array, BW(i), BY(b))
        return cls(length, array)

    @classmethod
    def symbolic(cls, name: str) -> Any:
        """Create a new, fully-symbolic Bytes."""
        return cls(
            z3.BitVec(f"{name}.length", 256),
            z3.Array(name, z3.BitVecSort(256), z3.BitVecSort(8)),
        )

    @abc.abstractmethod
    def __getitem__(self, i: uint256) -> uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        ...

    def slice(self, offset: uint256, size: uint256) -> ByteSlice:
        """Return a symbolic slice of this instance."""
        return ByteSlice(self, offset, size)

    def bigvector(self) -> z3.BitVecRef:
        """
        Return a single, large bitvector of this instance's bytes.

        Requires a concrete length.
        """
        return zconcat(*[self[BW(i)] for i in range(unwrap(self.length))])

    def require_concrete(self) -> bytes:
        """
        Unwrap this instance to bytes.

        Requires a concrete length and all-concrete values.
        """
        return bytes(unwrap(self[BW(i)]) for i in range(unwrap(self.length)))

    def evaluate(self, model: Model, model_completion: bool = False) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = unwrap(model.evaluate(self.length, True))
        result = ""
        for i in range(length):
            b = model.evaluate(self[BW(i)], model_completion)
            result += unwrap_bytes(b).hex() if is_concrete(b) else "??"
        return result


class FrozenBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Immutable."""

    def __getitem__(self, i: uint256) -> uint8:
        assert i.size() == 256
        return zget(self.array, i)


class ByteSlice(FrozenBytes):
    """A symbolic-length slice of symbolic bytes. Immutable."""

    def __init__(self, inner: Bytes, offset: uint256, size: uint256) -> None:
        """Create a new ByteSlice."""
        assert offset.size() == 256
        assert size.size() == 256
        self.inner = copy.deepcopy(inner)
        self.length = size
        self.offset = offset

    def __getitem__(self, i: uint256) -> uint8:
        assert i.size() == 256
        item = self.inner[self.offset + i]
        return zif(z3.ULT(i, self.length), item, BY(0))


class MutableBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Mutable."""

    def __getitem__(self, i: uint256) -> uint8:
        assert i.size() == 256
        item = zget(self.array, i)
        for k, v in self.writes:
            if isinstance(v, ByteSlice):
                destOffset = k
                item = zif(
                    zand(z3.UGE(i, destOffset), z3.ULT(i, destOffset + v.length)),
                    v[i - destOffset],
                    item,
                )
            else:
                item = zif(i == k, v, item)
        return zif(z3.ULT(i, self.length), item, BY(0))

    def __setitem__(self, i: uint256, v: uint8) -> None:
        assert i.size() == 256
        assert v.size() == 8
        self.length = simplify(zif(z3.ULT(i, self.length), self.length, i + 1))
        if len(self.writes) == 0:
            # Warning: passing writes through to the underlying array when there
            # are no custom writes is a good optimization (~12% speedup), but it
            # does create a performance cliff.
            self.array = zstore(self.array, i, v)
        else:
            self.writes.append((i, v))

    def graft(self, slice: ByteSlice, at: uint256) -> None:
        """Graft another Bytes into this one at the given offset."""
        assert at.size() == 256

        if is_concrete(slice.length) and unwrap(slice.length) == 0:
            # Short circuit e.g. in DELEGATECALL when retSize is zero.
            return

        self.length = simplify(
            zif(
                z3.ULT(at + slice.length - 1, self.length),
                self.length,
                at + slice.length,
            )
        )
        if len(self.writes) == 0 and is_concrete(slice.length):
            # Avoid creating custom writes when possible because of the
            # performance cliff (see above).
            for i in range(unwrap(slice.length)):
                self[at + BW(i)] = simplify(slice[BW(i)])
        else:
            self.writes.append((at, slice))
