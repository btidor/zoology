"""A symbolic adapter for SHA3 (Keccak) hashing."""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Iterable, Iterator, Literal, TypeAlias

from Crypto.Hash import keccak

from bytes import Bytes
from smt import (
    Array,
    Constraint,
    NarrowingError,
    Solver,
    Uint,
    Uint8,
    Uint256,
    describe,
    implies,
    mk_uint,
)

Uint128: TypeAlias = Uint[Literal[128]]


@dataclass
class SHA3:
    """
    Tracks SHA3 (Keccak) hashes.

    Within a single SHA3 instance, we symbolically constrain the state so that
    there are no hash *collisions* (other preimage attacks are legal).
    """

    # Caution: SHA3 hashes generally need to be consistent across contract
    # invocations and even across parallel universes. A singleton SHA3 instance
    # is probably the way to go.
    suffix: str = "*"

    # We model the SHA-3 function as a symbolic uninterpreted function from
    # n-byte inputs to 32-byte outputs. Z3 requires n to be constant for any
    # given function, so we store a mapping from `n -> func_n(x)`.
    hashes: dict[int, Array[Uint[Any], Uint256]] = field(default_factory=dict)

    # If the input has a symbolic length, we don't really know what it's going
    # to hash to. In this case, mint a new variable for the return value.
    free_digests: list[tuple[Bytes, Uint256]] = field(default_factory=list)

    constraints: list[Constraint] = field(default_factory=list)

    def __deepcopy__(self, memo: Any) -> SHA3:
        return SHA3(
            suffix=self.suffix,
            hashes=copy.copy(self.hashes),
            free_digests=copy.deepcopy(self.free_digests, memo),
            constraints=copy.deepcopy(self.constraints, memo),
        )

    def __getitem__(self, key: Bytes) -> Uint256:
        """Compute the SHA3 hash of a given key."""
        size = key.length.reveal()

        if size is None:
            result = Uint256(f"SHA3(?{len(self.free_digests)}){self.suffix}")
            self.free_digests.append((key, result))
            for key2, val2 in reversed(self.free_digests[:-1]):
                # HACK: to avoid introducing quantifiers, if this instance has a
                # symbolic length, we return a fixed 1024-byte vector. This is
                # an unsound assumption!
                result = (key.bigvector(1024) == key2.bigvector(1024)).ite(val2, result)
            return result

        if size == 0:
            digest = keccak.new(data=b"", digest_bits=256).digest()
            return Uint256(int.from_bytes(digest))

        if size not in self.hashes:
            self.hashes[size] = Array[mk_uint(size * 8), Uint256](
                f"SHA3({size}){self.suffix}"
            )

        free = self.hashes[size][key.bigvector(size)]
        if (data := key.reveal()) is not None:
            digest = keccak.new(data=data, digest_bits=256).digest()
            hash = Uint256(int.from_bytes(digest))
            self.constraints.append(free == hash)
        else:
            # ASSUMPTION: no hash may have more than 128 leading zero bits. This
            # avoids hash collisions between maps/arrays and ordinary storage
            # slots.
            self.constraints.append((free >> Uint256(128)).into(Uint128) != Uint128(0))
            hash = free

        for n, okey, oval in self.items():
            # ASSUMPTION: every hash digest is distinct, there are no collisions
            # ever.
            if n == size:
                self.constraints.append(implies(key.bigvector(n) != okey, hash != oval))
            else:
                self.constraints.append(hash != oval)

        return hash

    def items(self) -> Iterator[tuple[int, Uint[Any], Uint256]]:
        """
        Iterate over (n, key, value) tuples.

        Note: does not include free digests, which must be handled manually.
        """
        for n, array in self.hashes.items():
            for key in array.accessed:
                result = array.peek(key)
                yield (n, key, result)

    def constrain(self, solver: Solver) -> None:
        """Apply computed SHA3 constraints to the given solver instance."""
        # TODO: extend assumptions above to also constrain free digests
        for constraint in self.constraints:
            solver.add(constraint)

    def narrow(self, solver: Solver) -> None:
        """Apply concrete SHA3 constraints to a given model instance."""
        # TODO: narrowing is *unsound* because we concretize the key. It's
        # possible that a given evaluation of the key causes a future narrowing
        # step to fail while a different evaluation would allow it to succeed.
        # Therefore, narrowing errors should always bubble up as hard failures.
        for n, key, val in self.items():
            data = solver.evaluate(key).to_bytes(key.width // 8)
            hash = keccak.new(data=data, digest_bits=256)
            assert len(data) == n
            solver.add(key == key.__class__(int.from_bytes(data)))
            solver.add(val == Uint256(int.from_bytes(hash.digest())))
            if not solver.check():
                raise NarrowingError(data)

        for key, val in self.free_digests:
            data = key.evaluate(solver)
            hash = keccak.new(data=data, digest_bits=256)
            solver.add(key.length == Uint256(len(data)))
            for i, b in enumerate(data):
                solver.add(key[Uint256(i)] == Uint8(b))
            solver.add(val == Uint256(int.from_bytes(hash.digest())))
            if not solver.check():
                raise NarrowingError(data)

        assert solver.check()

    def printable(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable evaluation using the given model."""
        line = "SHA3"
        seen: set[str] = set()
        for _, key, val in self.items():
            k = "0x" + solver.evaluate(key).to_bytes(key.width // 8).hex()
            if k in seen:
                continue
            line += f"\t{k} "
            if len(k) > 34:
                yield line
                line = "\t"
            v = describe(Uint256(solver.evaluate(val)))
            line += f"-> {v}"
            yield line
            line = ""
            seen.add(k)

        if line == "":
            yield ""


def concrete_hash(data: bytes | str) -> Uint256:
    """Hash a concrete input and return the digest as a Uint256."""
    encoded = data if isinstance(data, bytes) else data.encode()
    digest = keccak.new(data=encoded, digest_bits=256).digest()
    return Uint256(int.from_bytes(digest))
