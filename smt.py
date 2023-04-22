"""Library for SMT solving. Currently a typed wrapper for Z3."""

from __future__ import annotations

import abc
import io
from typing import Any, Generic, Optional, Type, TypeVar, overload

import z3
from Crypto.Hash import keccak
from pysmt.fnode import FNode
from pysmt.smtlib.parser import get_formula

R = TypeVar("R", bound="z3.ExprRef")
S = TypeVar("S")

T = TypeVar("T", bound="BitVector")
U = TypeVar("U", bound="Uint")
V = TypeVar("V", bound="Symbolic[Any, Any]")

# Note: we use Z3Py expressions as our underlying representation because Z3's
# in-process simplifier is much more powerful than pySMT's. A well-simplified
# internal representation is important for debuggability.
#
# However, Bitwuzla (which we access through pySMT) is a much faster solver than
# Z3, so we convert to pySMT at solve time. The overhead is definitely worth it.


class Symbolic(abc.ABC, Generic[R, S]):
    """An SMT expression."""

    node: R

    def __init__(self, arg: str | R | S) -> None:
        """Create a new Symbolic."""
        raise NotImplementedError

    def __copy__(self: V) -> V:
        return self

    def __deepcopy__(self: V, memo: Any) -> V:
        return self

    @abc.abstractmethod
    def is_constant_literal(self) -> bool:
        """Check if the expression has a concrete value."""
        pass


# Creating the same BitVecSort instances over and over can create a lot of
# overhead. Create them once, upfront, instead.
BVSORT_8 = z3.BitVecSort(8)
BVSORT_160 = z3.BitVecSort(160)
BVSORT_256 = z3.BitVecSort(256)
BVSORT_257 = z3.BitVecSort(257)
BVSORT_512 = z3.BitVecSort(512)

ZERO_BIT = z3.BitVecVal(0, 1)


class BitVector(Symbolic[z3.BitVecRef, int]):
    """An SMT bitvector."""

    def __init__(self, arg: str | z3.BitVecRef | int):
        """Create a new BitVector."""
        if isinstance(arg, str):
            self.node = z3.BitVec(arg, self.length())
        elif isinstance(arg, z3.ExprRef):
            assert z3.is_bv(arg)
            assert (
                arg.size() == self.length()
            ), f"can't initialize {type(self).__name__} with {arg.size()} bits"
            result = z3.simplify(arg)
            assert isinstance(result, z3.BitVecRef)
            self.node = result
        elif isinstance(arg, int):
            sort = self._sort()
            # Borrowed from z3.BitVecVal(). Skipping the is_bv_sort() check
            # saves a little time.
            self.node = z3.BitVecNumRef(
                z3.Z3_mk_numeral(sort.ctx.ref(), str(arg), sort.ast),
                sort.ctx,
            )
        else:
            raise TypeError

    @classmethod
    @abc.abstractmethod
    def _sort(cls) -> z3.BitVecSortRef:
        raise NotImplementedError

    @classmethod
    @abc.abstractmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        raise NotImplementedError

    def __eq__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(self.node == other.node)

    def __ne__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(self.node != other.node)

    def __add__(self: T, other: T) -> T:
        return self.__class__(self.node + other.node)

    def __sub__(self: T, other: T) -> T:
        return self.__class__(self.node - other.node)

    def __mul__(self: T, other: T) -> T:
        return self.__class__(self.node * other.node)

    def is_constant_literal(self) -> bool:
        """Check if the bitvector has a concrete value."""
        result = z3.is_bv_value(self.node)
        assert type(result) == bool
        return result

    @overload
    def maybe_unwrap(self, into: Type[int] = int) -> int | None:
        ...

    @overload
    def maybe_unwrap(self, into: Type[bytes]) -> bytes | None:
        ...

    def maybe_unwrap(self, into: Type[int] | Type[bytes] = int) -> int | bytes | None:
        """Return the bitvector's underlying value, if a constant literal."""
        if not self.is_constant_literal():
            return None
        assert isinstance(self.node, z3.BitVecNumRef)

        if into == int:
            result = self.node.as_long()
            assert isinstance(result, int)
            return result
        elif into == bytes:
            result = self.node.as_long()
            assert isinstance(result, int)
            return result.to_bytes(self.length() // 8)
        else:
            raise TypeError(f"unexpected type: {into}")

    @overload
    def unwrap(
        self, into: Type[int] = int, msg: str = "unexpected symbolic value"
    ) -> int:
        ...

    @overload
    def unwrap(
        self, into: Type[bytes], msg: str = "unexpected symbolic value"
    ) -> bytes:
        ...

    def unwrap(
        self,
        into: Type[int] | Type[bytes] = int,
        msg: str = "unexpected symbolic value",
    ) -> int | bytes:
        """Unwrap the bitvector or raise an error."""
        if (u := self.maybe_unwrap(into)) is None:
            raise ValueError(msg)
        return u

    def describe(self) -> str:
        """
        Produce a human-readable description of the given bitvector.

        For concrete bitvectors, returns a result in hexadecimal. Long values are
        broken into 256-bit chunks using dot syntax, e.g. "0x[1234.1]".

        For symbolic bitvectors, returns a hash based on the input variables.
        """
        return BitVector._describe(self.node)

    @classmethod
    def _describe(cls, node: z3.ExprRef) -> str:
        if z3.is_bv_value(node):
            assert isinstance(node, z3.BitVecNumRef)
            v = node.as_long()
            if v < (1 << 256):
                return hex(v)
            p = []
            while v > 0:
                b = v & ((1 << 256) - 1)
                p.append(hex(b)[2:])
                v >>= 256
            return f"0x[{'.'.join(reversed(p))}]"
        else:
            digest = keccak.new(data=node.sexpr().encode(), digest_bits=256).digest()
            return "#" + digest[:3].hex()


class Uint(BitVector):
    """A bitvector representing an unsigned integer."""

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(z3.ULT(self.node, other.node))

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(z3.ULE(self.node, other.node))

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(z3.UDiv(self.node, other.node))

    def __mod__(self: T, other: T) -> T:
        return self.__class__(z3.URem(self.node, other.node))

    def __lshift__(self: T, other: T) -> T:
        return self.__class__(self.node << other.node)

    def __rshift__(self: T, other: T) -> T:
        return self.__class__(z3.LShR(self.node, other.node))

    def __and__(self: T, other: T) -> T:
        return self.__class__(self.node & other.node)

    def __or__(self: T, other: T) -> T:
        return self.__class__(self.node | other.node)

    def __xor__(self: T, other: T) -> T:
        return self.__class__(self.node ^ other.node)

    def __invert__(self: T) -> T:
        return self.__class__(~self.node)

    def into(self, into: Type[U]) -> U:
        """Truncate or zero-extend the bitvector into a different type."""
        if into.length() > self.length():
            return into(z3.ZeroExt(into.length() - self.length(), self.node))
        else:
            result = z3.Extract(into.length() - 1, 0, self.node)
            assert isinstance(result, z3.BitVecRef)
            return into(result)


class Sint(BitVector):
    """A bitvector representing a signed integer."""

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(self.node < other.node)

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(self.node <= other.node)

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(self.node / other.node)

    def __mod__(self: T, other: T) -> T:
        return self.__class__(z3.SRem(self.node, other.node))


class Uint8(Uint):
    """A uint8."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_8

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 8


class Uint160(Uint):
    """A uint160."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_160

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 160


class Uint256(Uint):
    """A uint256."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_256

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 256

    @classmethod
    def from_bytes(cls, *args: Uint8) -> Uint256:
        """Create a new Uint256 from a list of 32 Uint8s."""
        assert len(args) == 32
        result = z3.Concat(*[a.node for a in args])
        assert isinstance(result, z3.BitVecRef)
        return Uint256(result)

    @classmethod
    def overflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a + b does not overflow."""
        result = a.into(Uint257) + b.into(Uint257)
        sign = z3.Extract(256, 256, result.node)
        return Constraint(sign == ZERO_BIT)

    @classmethod
    def underflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a - b does not underflow."""
        return a >= b

    def as_signed(self) -> Sint256:
        """Reinterpret as a signed int256."""
        return Sint256(self.node)


class Uint257(Uint):
    """A uint257."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_257

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 257


class Uint512(Uint):
    """A uint512."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_512

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 512


class Sint256(Sint):
    """A signed int256."""

    @classmethod
    def _sort(cls) -> z3.BitVecSortRef:
        return BVSORT_256

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 256

    def as_unsigned(self) -> Uint256:
        """Reinterpret as an unsigned uint256."""
        return Uint256(self.node)

    def __lshift__(self: T, other: Uint256) -> T:
        return self.__class__(self.node << other.node)

    def __rshift__(self: T, other: Uint256) -> T:
        return self.__class__(self.node >> other.node)


class Constraint(Symbolic[z3.BoolRef, bool]):
    """A symbolic boolean value representing true or false."""

    def __init__(self, arg: str | z3.BoolRef | bool):
        """Create a new Constraint."""
        self._fnode: Optional[FNode] = None
        if isinstance(arg, str):
            self.node = z3.Bool(arg)
        elif isinstance(arg, z3.ExprRef):
            assert z3.is_bool(arg)
            result = z3.simplify(arg)
            assert isinstance(result, z3.BoolRef)
            self.node = result
        elif isinstance(arg, bool):
            self.node = z3.BoolVal(arg)
        else:
            raise TypeError

    def __bool__(self) -> bool:
        # Footgun: it's really easy to accidentally create a Constraint and try
        # to use it in a boolean context. Unfortunately, the Constraint will
        # always be truthy, so raise an error instead.
        #
        # > a, b = Uint8(...), Uint8(...)
        # > if a > b:
        # >     ...
        # > else:
        # >     ... # unreachable!
        #
        raise TypeError("implicit concretization of constraint")

    @classmethod
    def all(cls, *constraints: Constraint) -> Constraint:
        """Return the AND of all given constraints."""
        result = z3.And(*(c.node for c in constraints))
        assert isinstance(result, z3.BoolRef)
        return Constraint(result)

    @classmethod
    def any(cls, *constraints: Constraint) -> Constraint:
        """Return the OR of all given constraints."""
        result = z3.Or(*(c.node for c in constraints))
        assert isinstance(result, z3.BoolRef)
        return Constraint(result)

    def __invert__(self) -> Constraint:
        result = z3.Not(self.node)
        assert isinstance(result, z3.BoolRef)
        return Constraint(result)

    def ite(self, then: V, else_: V) -> V:
        """Return a symbolic value: `then` if true, `else_` if false."""
        return then.__class__(z3.If(self.node, then.node, else_.node))

    def is_constant_literal(self) -> bool:
        """Check if the constraint has a concrete value."""
        result = z3.is_true(self.node) or z3.is_false(self.node)
        assert type(result) == bool
        return result

    def maybe_unwrap(self) -> bool | None:
        """Return the constraint's underlying value, if a constant literal."""
        if z3.is_true(self.node):
            return True
        elif z3.is_false(self.node):
            return False
        else:
            return None

    def unwrap(self, msg: str = "unexpected symbolic value") -> bool:
        """Unwrap the constraint or raise an error."""
        if (value := self.maybe_unwrap()) is None:
            raise ValueError(msg)
        return value

    def as_pysmt(self) -> FNode:
        """
        Return the pySMT representation of this Constraint.

        Caches conversion results for performance.
        """
        if self._fnode is None:
            # FYI, this Z3 -> pySMT conversion process only works for boolean
            # constraints, not arbitrary expressions ¯\_(ツ)_/¯
            smtlib = z3.Z3_benchmark_to_smtlib_string(
                self.node.ctx_ref(),
                None,
                None,
                None,
                None,
                0,
                None,
                self.node.as_ast(),
            )

            # The *_i versions of these operators are an internal Z3
            # optimization; they function identically to the standard SMTLIB
            # ops:
            # https://github.com/Z3Prover/z3/blob/0b5c38d/src/api/z3_api.h#L394-L407
            for op in ["bvsdiv", "bvudiv", "bvsrem", "bvurem", "bvsmod"]:
                smtlib = smtlib.replace(f"{op}_i", op)

            self._fnode = get_formula(io.StringIO(smtlib))

        return self._fnode
