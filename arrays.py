"""Types for representing array-like symbolic state."""

from __future__ import annotations

import abc
import copy
from typing import Any, Iterable, List, Tuple, TypeAlias, Union

import z3

from symbolic import (
    BW,
    BY,
    describe,
    is_bitvector,
    is_concrete,
    simplify,
    uint8,
    uint256,
    unwrap,
    unwrap_bytes,
    zand,
    zeval,
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

    def printable_diff(
        self, name: str, model: z3.ModelRef, original: Array
    ) -> Iterable[str]:
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
                k = describe(zeval(model, key, True))
                v = describe(zeval(model, value, True))
                p = describe(zeval(model, prior, True)) if prior is not None else None
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
                    line += " (no change)" if value == prior else f" (from {prior})"
                yield line
                line = ""

        if line == "":
            yield ""


BytesWrite: TypeAlias = Union[
    Tuple[uint256, uint8],
    Tuple[Tuple[uint256, uint256, uint256], "Bytes"],
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
        return MutableBytes(
            z3.BitVec(f"{name}.length", 256),
            z3.Array(name, z3.BitVecSort(256), z3.BitVecSort(8)),
        )

    @abc.abstractmethod
    def __getitem__(self, i: uint256) -> uint8:
        ...

    def require_concrete(self) -> bytes:
        """Unwrap this concrete-valued instance to bytes."""
        return bytes(unwrap(self[BW(i)]) for i in range(unwrap(self.length)))

    def evaluate(self, model: z3.ModelRef, model_completion: bool = False) -> str:
        """Use a model to evaluate this instance as a hexadecimal string."""
        length = unwrap(zeval(model, self.length, True))
        result = ""
        for i in range(length):
            b = zeval(model, self[BW(i)], model_completion)
            result += unwrap_bytes(b).hex() if is_concrete(b) else "??"
        return result


class FrozenBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Immutable."""

    def __getitem__(self, i: uint256) -> uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        assert i.size() == 256
        return zget(self.array, i)


class MutableBytes(Bytes):
    """A symbolic-length sequence of symbolic bytes. Mutable."""

    def __getitem__(self, i: uint256) -> uint8:
        """
        Return the byte at the given symbolic index.

        Reads past the end of the bytestring return zero.
        """
        assert i.size() == 256
        item = zget(self.array, i)
        for k, v in self.writes:
            if isinstance(k, tuple):
                assert isinstance(v, Bytes)
                destOffset, offset, size = k
                item = zif(
                    zand(z3.UGE(i, destOffset), z3.ULT(i, destOffset + size)),
                    v[offset + (i - destOffset)],
                    item,
                )
            else:
                assert not isinstance(v, Bytes)
                item = zif(i == k, v, item)
        return zif(z3.ULT(i, self.length), item, BY(0))

    def __setitem__(self, i: uint256, v: uint8) -> None:
        """Write the byte at the given symbolic index."""
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

    def splice_from(
        self,
        other: Bytes,
        destOffset: uint256,
        offset: uint256,
        size: uint256,
    ) -> None:
        """Splice another Bytes into this one using the given offsets."""
        assert offset.size() == 256
        assert destOffset.size() == 256
        assert size.size() == 256
        self.length = simplify(
            zif(
                z3.ULT(destOffset + size - 1, self.length),
                self.length,
                destOffset + size,
            )
        )
        if len(self.writes) == 0 and is_concrete(size):
            # Avoid creating custom writes when possible because of the
            # performance cliff (see above).
            for i in range(unwrap(size)):
                self[destOffset + BW(i)] = simplify(other[offset + BW(i)])
        else:
            self.writes.append(((destOffset, offset, size), copy.deepcopy(other)))