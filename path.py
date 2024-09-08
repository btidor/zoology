"""
A library for representing the path constraint.

Includes special logic for handling Keccak-256 hashing.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Literal, Self, TypeAlias

from bytes import BYTES, Bytes
from smt import (
    EMPTY_DIGEST,
    Constraint,
    NarrowingError,
    Solver,
    Substitutions,
    Uint,
    Uint256,
    concat_bytes,
    concrete_hash,
    iff,
    implies,
    prequal,
)

Uint128: TypeAlias = Uint[Literal[128]]


@dataclass
class Path:
    """The symbolic constraints associated with a path."""

    # Each path is numbered based on the forks followed to reach it. Each JUMPI
    # is a bit, 1 if taken, 0 if not; MSB-first with a leading 1 prepended.
    id: int = 1

    # The main symbolic constraint. This constraint is updated at each JUMPI
    # instruction.
    constraint: Constraint = field(default_factory=lambda: Constraint(True))

    # Whether any mutations have been performed on this path, i.e. if it's legal
    # to execute during a STATICCALL.
    static: bool = True

    # When performing SHA3 hashing, we create symbolic constraints to assert
    # that there are no hash collisions. To do this, we log every SHA3 call in
    # the path.
    #
    # NOTE: other types of preimage attacks are legal!
    #
    free: list[tuple[Bytes, Uint256]] = field(default_factory=list)
    symbolic: list[tuple[Uint[Any], Uint256]] = field(default_factory=list)
    concrete: dict[bytes, tuple[Uint[Any], Uint256]] = field(default_factory=dict)

    def __deepcopy__(self, memo: Any) -> Self:
        return self.__class__(
            constraint=self.constraint,
            id=self.id,
            static=self.static,
            free=copy.copy(self.free),
            symbolic=copy.copy(self.symbolic),
            concrete=copy.copy(self.concrete),
        )

    def px(self) -> str:
        """Return a human-readable version of the path ID."""
        return "Px" + hex(self.id)[2:].upper()

    def keccak256(self, input: Bytes) -> Uint256:
        """
        Compute the Keccak-256 hash of a given key.

        This method mutates the path constraint. It should only be called before
        constraining and narrowing!
        """
        if (size := input.length.reveal()) is None:
            # Case I: Free Digest (symbolic length, symbolic data).
            digest = Uint256(f"DIGEST:F{len(self.free)}")
            self.free.append((input, digest))

            # ASSUMPTION: no hash may have more than 128 leading zero bits. This
            # avoids hash collisions between maps/arrays and ordinary storage
            # slots.
            constraint = (digest >> Uint256(128)).into(Uint128) != Uint128(0)
            # ASSUMPTION: every hash digest is distinct. This is SHA-3, there
            # are no collisions, ever. (We check free digests for collisions
            # during narrowing, when we can concretize the length.)
            constraint &= iff(input.length == Uint256(0), digest == EMPTY_DIGEST)
            for data, (_, digest2) in self.concrete.items():
                constraint &= implies(
                    input.length != Uint256(len(data)), digest != digest2
                )
                constraint &= implies(
                    digest == digest2, input.length == Uint256(len(data))
                )
            for vector2, digest2 in self.symbolic:
                constraint &= implies(
                    input.length != Uint256(vector2.width // 8), digest != digest2
                )
                constraint &= implies(
                    digest == digest2, input.length == Uint256(vector2.width // 8)
                )
            for input2, digest2 in self.free[:-1]:
                constraint &= implies(input.length != input2.length, digest != digest2)
                constraint &= implies(digest == digest2, input.length == input2.length)
            self.constraint &= constraint
            return digest
        elif size == 0:
            # Case II: Empty Digest (zero length).
            return EMPTY_DIGEST
        elif (data := input.reveal()) is None:
            # Case III: Symbolic Digest (concrete length, symbolic data).
            vector = input.bigvector()
            for other, digest in self.symbolic:
                if prequal(vector, other):
                    return digest
            digest = Uint256(f"DIGEST:S{len(self.symbolic)}")
            self.symbolic.append((vector, digest))

            constraint = (digest >> Uint256(128)).into(Uint128) != Uint128(0)
            constraint &= digest != EMPTY_DIGEST
            for data, (vector2, digest2) in self.concrete.items():
                if vector.width // 8 == len(data):
                    constraint &= iff(vector == vector2, digest == digest2)
                else:
                    constraint &= digest != digest2
            for vector2, digest2 in self.symbolic[:-1]:
                if vector.width == vector2.width:
                    constraint &= iff(vector == vector2, digest == digest2)
                else:
                    constraint &= digest != digest2
            for input2, digest2 in self.free:
                constraint &= implies(
                    input2.length != Uint256(vector.width // 8), digest != digest2
                )
                constraint &= implies(
                    digest == digest2, input2.length == Uint256(vector.width // 8)
                )
                for i in range(vector.width // 8):
                    constraint &= implies(
                        digest == digest2, input[Uint256(i)] == input2[Uint256(i)]
                    )
            self.constraint &= constraint
            return digest
        else:
            # Case IV: Concrete Digest (concrete length, concrete data).
            constraint = Constraint(True)
            if data not in self.concrete:
                self.concrete[data] = (input.bigvector(), concrete_hash(data))
                vector, digest = self.concrete[data]
                for vector2, digest2 in self.symbolic:
                    if vector.width == vector2.width:
                        constraint &= iff(vector == vector2, digest == digest2)
                    else:
                        constraint &= digest != digest2
                for input2, digest2 in self.free:
                    constraint &= implies(
                        input2.length != Uint256(len(data)), digest != digest2
                    )
                    constraint &= implies(
                        digest == digest2, input2.length == Uint256(len(data))
                    )
                    for i in range(len(data)):
                        constraint &= implies(
                            digest == digest2, input[Uint256(i)] == input2[Uint256(i)]
                        )
            self.constraint &= constraint
            return self.concrete[data][1]

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
            vector = concat_bytes(*(key[Uint256(i)] for i in range(length)))
            vectors.append(vector)
            for (key2, digest2), length2 in zip(self.free[i + 1 :], lengths[i + 1 :]):
                if length != length2:
                    continue
                vector2 = concat_bytes(*(key2[Uint256(i)] for i in range(length)))
                solver.add(iff(vector == vector2, digest == digest2))
            if not solver.check():
                raise NarrowingError(None)

        for i, ((key, digest), vector2) in enumerate(zip(self.free, vectors)):
            if not (data := key.evaluate(solver)):
                continue  # empty digest, handled in constraining

            vector1 = concat_bytes(*(BYTES[b] for b in data))
            digest1 = concrete_hash(data)

            constraint = key.length == Uint256(len(data))
            for i, b in enumerate(data):
                constraint &= key[Uint256(i)] == BYTES[b]
            constraint &= digest == digest1

            for vector2, digest2 in concretized:
                if vector1.width == vector2.width:
                    constraint &= iff(vector1 == vector2, digest1 == digest2)
                else:
                    constraint &= digest1 != digest2

            solver.add(constraint)
            if not solver.check():
                raise NarrowingError(data)
            concretized.append((vector1, digest1))

        return concretized

    def update_substitutions(self) -> Substitutions:
        """After term substitution, handle newly concrete hashes."""
        subs: Substitutions = []

        symbolic = list[tuple[Uint[Any], Uint256]]()
        for vector, digest in self.symbolic:
            if (v := vector.reveal()) is None:
                symbolic.append((vector, digest))
            else:
                data = v.to_bytes(vector.width // 8)
                concrete = concrete_hash(data)
                subs.append((digest, concrete))
                self.concrete[data] = (vector, concrete)
        self.symbolic = symbolic

        free = list[tuple[Bytes, Uint256]]()
        for input, digest in self.free:
            if (data := input.reveal()) is None:
                free.append((input, digest))
            elif data:
                concrete = concrete_hash(data)
                subs.append((digest, concrete))
                self.concrete[data] = (input.bigvector(), concrete)
        self.free = free
        return subs
