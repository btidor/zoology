"""A symbolic adapter for SHA3 (Keccak) hashing."""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, Iterator, List, Tuple

from Crypto.Hash import keccak
from pysmt.fnode import FNode
from pysmt.shortcuts import BV, BVExtract, Equals, Implies, NotEquals, Select, Symbol
from pysmt.typing import ArrayType, BVType

from arrays import Bytes
from smt import Constraint, Uint8, Uint256
from solver import Solver


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
    hashes: Dict[int, FNode] = field(default_factory=dict)

    # If the input has a symbolic length, we don't really know what it's going
    # to hash to. In this case, mint a new variable for the return value.
    free_digests: List[Tuple[Bytes, Uint256]] = field(default_factory=list)

    accessed: Dict[int, List[Bytes]] = field(default_factory=dict)

    digest_constraints: List[Constraint] = field(default_factory=list)

    def __deepcopy__(self, memo: Any) -> SHA3:
        return SHA3(
            suffix=self.suffix,
            hashes=copy.copy(self.hashes),
            free_digests=copy.deepcopy(self.free_digests, memo),
            accessed=copy.deepcopy(self.accessed, memo),
            digest_constraints=copy.deepcopy(self.digest_constraints, memo),
        )

    def __getitem__(self, key: Bytes) -> Uint256:
        """Compute the SHA3 hash of a given key."""
        size = key.length.maybe_unwrap()

        if size is None:
            result = Uint256(f"SHA3(?{len(self.free_digests)}){self.suffix}")
            self.free_digests.append((key, result))
            for key2, val2 in reversed(self.free_digests[:-1]):
                result = Constraint(Equals(key._bigvector(), key2._bigvector())).ite(
                    val2, result
                )
            return result

        if size == 0:
            digest = keccak.new(data=b"", digest_bits=256).digest()
            return Uint256(int.from_bytes(digest))

        if size not in self.hashes:
            self.hashes[size] = Symbol(
                f"SHA3({size}){self.suffix}",
                ArrayType(BVType(size * 8), BVType(256)),
            )
            self.accessed[size] = []

        self.accessed[size].append(key)

        if (data := key.maybe_unwrap()) is not None:
            digest = keccak.new(data=data, digest_bits=256).digest()
            symbolic = Uint256(int.from_bytes(digest))
            self.digest_constraints.append(
                Constraint(
                    Equals(Select(self.hashes[size], key._bigvector()), symbolic.node)
                )
            )
            return symbolic
        else:
            return Uint256(Select(self.hashes[size], key._bigvector()))

    def items(self) -> Iterator[Tuple[int, Bytes, Uint256]]:
        """
        Iterate over (n, key, value) tuples.

        Note: does not include free digests, which must be handled manually.
        """
        for n, array in self.hashes.items():
            for key in self.accessed[n]:
                yield (n, key, Uint256(Select(array, key._bigvector())))

    def constrain(self, solver: Solver) -> None:
        """Apply computed SHA3 constraints to the given solver instance."""
        for n1, key1, val1 in self.items():
            # Assumption: no hash may have more than 128 leading zero bits. This
            # avoids hash collisions between maps/arrays and ordinary storage
            # slots.
            solver.assert_and_track(
                Constraint(NotEquals(BVExtract(val1.node, 128, 255), BV(0, 128)))
            )

            for n2, key2, val2 in self.items():
                # Assumption: every hash digest is distinct, there are no
                # collisions ever.
                if n1 == n2:
                    solver.assert_and_track(
                        Constraint(
                            Implies(
                                NotEquals(key1._bigvector(), key2._bigvector()),
                                NotEquals(val1.node, val2.node),
                            )
                        )
                    )
                else:
                    solver.assert_and_track(val1 != val2)

        # TODO: extend these assumptions to support free digests

        for constraint in self.digest_constraints:
            solver.assert_and_track(constraint)

    def narrow(self, solver: Solver) -> None:
        """Apply concrete SHA3 constraints to a given model instance."""
        for n, key, val in self.items():
            data = key.evaluate(solver)
            hash = keccak.new(data=data, digest_bits=256)
            solver.assert_and_track(
                Constraint(Equals(key._bigvector(), BV(int.from_bytes(data), n * 8)))
            )
            solver.assert_and_track(val == Uint256(int.from_bytes(hash.digest())))
            assert solver.check()

        for key, val in self.free_digests:
            data = key.evaluate(solver)
            hash = keccak.new(data=data, digest_bits=256)
            solver.assert_and_track(key.length == Uint256(len(data)))
            for i, b in enumerate(data):
                solver.assert_and_track(key[Uint256(i)] == Uint8(b))
            solver.assert_and_track(val == Uint256(int.from_bytes(hash.digest())))
            assert solver.check()

    def printable(self, solver: Solver) -> Iterable[str]:
        """Yield a human-readable evaluation using the given model."""
        line = "SHA3"
        seen = set()
        for _, key, val in self.items():
            k = "0x" + key.describe(solver)
            if k in seen:
                continue
            line += f"\t{k} "
            if len(k) > 34:
                yield line
                line = "\t"
            v = solver.evaluate(val, True).describe()
            line += f"-> {v}"
            yield line
            line = ""
            seen.add(k)

        if line == "":
            yield ""
