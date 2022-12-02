from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterator, List, Tuple, cast

import z3
from Crypto.Hash import keccak

from _symbolic import (
    BW,
    Constraint,
    IntrospectableArray,
    describe_bv,
    do_check,
    require_concrete,
    simplify_bv,
)


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
    hashes: Dict[int, IntrospectableArray] = field(default_factory=dict)

    digest_constraints: List[Constraint] = field(default_factory=list)

    def copy(self) -> SHA3:
        """Return a deep copy of this instance."""
        return SHA3(self.suffix, self.hashes.copy())

    def __getitem__(self, key: z3.BitVecRef) -> z3.BitVecRef:
        """Compute the SHA3 hash of a given key."""
        size = key.size() // 8
        assert key.size() % 8 == 0
        if size not in self.hashes:
            self.hashes[size] = IntrospectableArray(
                f"SHA3({size}){self.suffix}",
                z3.BitVecSort(size * 8),
                z3.BitVecSort(256),
            )

        key = simplify_bv(key)
        if z3.is_bv_value(key):
            digest = keccak.new(
                data=require_concrete(key).to_bytes(size, "big"), digest_bits=256
            ).digest()
            symbolic = BW(int.from_bytes(digest, "big"))
            self.digest_constraints.append(self.hashes[size][key] == symbolic)
            return symbolic

        return self.hashes[size][key]

    def items(self) -> Iterator[Tuple[int, z3.BitVecRef, z3.BitVecRef]]:
        """Iterate over (n, key, value) tuples."""
        for n, arr in self.hashes.items():
            for key in arr.accessed:
                yield (n, key, cast(z3.BitVecRef, arr.array[key]))

    def constrain(self, solver: z3.Optimize) -> None:
        """Apply computed SHA3 constraints to the given solver instance."""
        for n, key, val in self.items():
            fp = describe_bv(key)

            # Assumption: no hash may have more than 128 leading zero bits. This
            # avoids hash collisions between maps/arrays and ordinary storage
            # slots.
            solver.assert_and_track(
                z3.Extract(255, 128, val) != 0,
                f"SHA3({n}).NLZ[{fp}]{self.suffix}",
            )

            for _, key2, val2 in self.items():
                fp2 = describe_bv(key2)

                # Assumption: every hash digest is distinct, there are no
                # collisions ever.
                solver.assert_and_track(
                    z3.Implies(key != key2, val != val2),
                    f"SHA3({n}).DISTINCT[{fp},{fp2}]{self.suffix}",
                )

        for i, constraint in enumerate(self.digest_constraints):
            solver.assert_and_track(constraint, f"SHA3.DIGEST{i}{self.suffix}")
            pass

    def concretize(self, solver: z3.Optimize, model: z3.ModelRef) -> z3.ModelRef:
        """Apply concrete SHA3 constraints to a given model instance."""
        hashes: Dict[bytes, bytes] = {}
        for n, key, val in self.items():
            ckey = require_concrete(model.eval(key, True))
            data = ckey.to_bytes(n, "big")
            hash = keccak.new(data=data, digest_bits=256)
            digest = int.from_bytes(hash.digest(), "big")
            hashes[data] = hash.digest()
            solver.assert_and_track(key == ckey, f"SHAKEY{n}{self.suffix}")
            solver.assert_and_track(
                val == BW(digest),
                f"SHAVAL{n}{self.suffix}",
            )
            assert do_check(solver)
            model = solver.model()

        if len(hashes) > 0:
            print(f"SHA3", end="")
            keys = sorted(hashes.keys())
            for k in keys:
                if len(k) == 64:
                    a = hex(int.from_bytes(k[:32], "big"))
                    b = hex(int.from_bytes(k[32:], "big"))
                    sk = f"0x[{a[2:]}.{b[2:]}]"
                else:
                    sk = hex(int.from_bytes(k, "big"))
                print(f"\t{sk} ", end="")
                if len(sk) > 34:
                    print("\n\t", end="")
                print(f"-> 0x{hashes[k].hex()}")

        return model
