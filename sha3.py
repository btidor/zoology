"""A symbolic adapter for SHA3 (Keccak) hashing."""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Self

from Crypto.Hash import keccak

from bytes import BYTES, Bytes
from smt import (
    Constraint,
    NarrowingError,
    Solver,
    Uint,
    Uint8,
    Uint128,
    Uint256,
)


def concrete_hash(data: bytes | str) -> Uint256:
    """Hash a concrete input and return the digest as a Uint256."""
    encoded = data if isinstance(data, bytes) else data.encode()
    digest = keccak.new(data=encoded, digest_bits=256).digest()
    return Uint256(int.from_bytes(digest))


EMPTY_DIGEST = concrete_hash(b"")


@dataclass(slots=True)
class SHA3:
    """
    Tracks SHA3 (Keccak) hashes.

    Within a single SHA3 instance, we symbolically constrain the state so that
    there are no hash *collisions* (other preimage attacks are legal).
    """

    free: list[tuple[Bytes, Uint256]] = field(
        default_factory=list[tuple[Bytes, Uint256]]
    )
    symbolic: list[tuple[Uint[Any], Uint256]] = field(
        default_factory=list[tuple[Uint[Any], Uint256]]
    )
    concrete: dict[bytes, tuple[Uint[Any], Uint256]] = field(
        default_factory=dict[bytes, tuple[Uint[Any], Uint256]]
    )

    def __deepcopy__(self, memo: Any) -> Self:
        result = copy.copy(self)
        result.free = copy.copy(self.free)
        result.symbolic = copy.copy(self.symbolic)
        result.concrete = copy.copy(self.concrete)
        return result

    def hash(self, input: Bytes) -> tuple[Uint256, Constraint]:
        """
        Compute the SHA3 hash of a given key.

        This method should only be called before constraining and narrowing!
        """
        if (size := input.length.reveal()) is None:
            # Case I: Free Digest (symbolic length, symbolic data).
            digest = Uint256(f"DIGEST@F{len(self.free)}")
            self.free.append((input, digest))

            # ASSUMPTION: no hash may have more than 127 leading zero bits. This
            # avoids hash collisions between maps/arrays and ordinary storage
            # slots.
            digest._term.min = 1 << 128  # pyright: ignore[reportPrivateUsage]
            constraint = (digest >> Uint256(128)).into(Uint128) != Uint128(0)
            # ASSUMPTION: every hash digest is distinct. This is SHA-3, there
            # are no collisions, ever. (We check free digests for collisions
            # during narrowing, when we can concretize the length.)
            constraint &= (input.length == Uint256(0)).implies(digest == EMPTY_DIGEST)
            for data, (_, digest2) in self.concrete.items():
                constraint &= (input.length != Uint256(len(data))).implies(
                    digest != digest2
                )
                constraint &= (digest == digest2).implies(
                    input.length == Uint256(len(data))
                )
            for vector2, digest2 in self.symbolic:
                constraint &= (input.length != Uint256(vector2.width // 8)).implies(
                    digest != digest2,
                )
                constraint &= (digest == digest2).implies(
                    input.length == Uint256(vector2.width // 8),
                )
            for input2, digest2 in self.free[:-1]:
                constraint &= (input.length != input2.length).implies(digest != digest2)
                constraint &= (digest == digest2).implies(input.length == input2.length)
            return (digest, constraint)
        elif size == 0:
            # Case II: Empty Digest (zero length).
            return (EMPTY_DIGEST, Constraint(True))
        elif (data := input.reveal()) is None:
            # Case III: Symbolic Digest (concrete length, symbolic data).
            vector = input.bigvector()
            for other, digest in self.symbolic:
                if prequal(vector, other):
                    return (digest, Constraint(True))
            digest = Uint256(f"DIGEST@S{len(self.symbolic)}")
            self.symbolic.append((vector, digest))

            # ASSUMPTION: not too many leading zeroes (see above).
            digest._term.min = 1 << 128  # pyright: ignore[reportPrivateUsage]
            constraint = (digest >> Uint256(128)).into(Uint128) != Uint128(0)
            constraint &= digest != EMPTY_DIGEST

            for data, (vector2, digest2) in self.concrete.items():
                if vector.width // 8 == len(data):
                    constraint &= (vector == vector2).iff(digest == digest2)
                else:
                    constraint &= digest != digest2
            for vector2, digest2 in self.symbolic[:-1]:
                if vector.width == vector2.width:
                    constraint &= (vector == vector2).iff(digest == digest2)
                else:
                    constraint &= digest != digest2
            for input2, digest2 in self.free:
                constraint &= (input2.length != Uint256(vector.width // 8)).implies(
                    digest != digest2
                )
                constraint &= (digest == digest2).implies(
                    input2.length == Uint256(vector.width // 8)
                )
                for i in range(vector.width // 8):
                    constraint &= (digest == digest2).implies(
                        input[Uint256(i)] == input2[Uint256(i)]
                    )
            return (digest, constraint)
        else:
            # Case IV: Concrete Digest (concrete length, concrete data).
            constraint = Constraint(True)
            if data not in self.concrete:
                self.concrete[data] = (input.bigvector(), concrete_hash(data))
                vector, digest = self.concrete[data]
                for vector2, digest2 in self.symbolic:
                    if vector.width == vector2.width:
                        constraint &= (vector == vector2).iff(digest == digest2)
                    else:
                        constraint &= digest != digest2
                for input2, digest2 in self.free:
                    constraint &= (input2.length != Uint256(len(data))).implies(
                        digest != digest2
                    )
                    constraint &= (digest == digest2).implies(
                        input2.length == Uint256(len(data))
                    )
                    for i in range(len(data)):
                        constraint &= (digest == digest2).implies(
                            input[Uint256(i)] == input2[Uint256(i)]
                        )
            return (self.concrete[data][1], constraint)

    def narrow(self, solver: Solver) -> list[tuple[Uint[Any], Uint256]]:
        """
        Apply concrete SHA3 constraints to a given model instance.

        Narrowing is *unsound* because we concretize the hash inputs and
        outputs. Narrowing errors should always bubble up as a hard failure of
        the analysis.
        """
        concretized = list[tuple[Uint[Any], Uint256]]()
        for vector, digest in self.symbolic:
            evaluation = solver.evaluate(vector)
            data = evaluation.to_bytes(vector.width // 8)
            vector1 = vector.__class__(evaluation)
            digest1 = concrete_hash(data)

            solver.add((vector == vector1) & (digest == digest1))
            if not solver.check():
                raise NarrowingError(data)
            concretized.append((vector1, digest1))

        vectors = list[Uint[Any]]()
        lengths = [solver.evaluate(k.length) for (k, _) in self.free]
        for i, ((key, digest), length) in enumerate(zip(self.free, lengths)):
            if length == 0:
                continue  # handled with symbolic constraints
            vector = Uint8.concat(*(key[Uint256(i)] for i in range(length)))
            vectors.append(vector)
            for (key2, digest2), length2 in zip(self.free[i + 1 :], lengths[i + 1 :]):
                if length != length2:
                    continue
                vector2 = Uint8.concat(*(key2[Uint256(i)] for i in range(length)))
                solver.add((vector == vector2).iff(digest == digest2))
            if not solver.check():
                raise NarrowingError(None)

        for i, ((key, digest), vector2) in enumerate(zip(self.free, vectors)):
            if not (data := key.evaluate(solver)):
                continue  # empty digest, handled in constraining

            vector1 = Uint8.concat(*(BYTES[b] for b in data))
            digest1 = concrete_hash(data)

            constraint = key.length == Uint256(len(data))
            for i, b in enumerate(data):
                constraint &= key[Uint256(i)] == Uint8(b)
            constraint &= digest == digest1

            for vector2, digest2 in concretized:
                if vector1.width == vector2.width:
                    constraint &= (vector1 == vector2).iff(digest1 == digest2)
                else:
                    constraint &= digest1 != digest2

            solver.add(constraint)
            if not solver.check():
                raise NarrowingError(data)
            concretized.append((vector1, digest1))

        return concretized


def prequal[N: int](a: Uint[N], b: Uint[N]) -> bool:
    """
    Quickly check if two bitvectors are equal.

    If the two nodes are equal after simplification, return True. Otherwise,
    return False (they may still be equal, but that requires a call to the
    solver to determine).
    """
    return (a == b).reveal() is True
