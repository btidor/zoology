"""Library for SMT solving. Currently a typed wrapper for pySMT."""

from __future__ import annotations

import abc
from typing import Any, Generic, Literal, Optional, Type, TypeVar, Union, overload

from Crypto.Hash import keccak
from pysmt.fnode import FNode
from pysmt.shortcuts import (
    BV,
    BVSLE,
    BVSLT,
    BVULE,
    BVULT,
    And,
    Bool,
    BVAdd,
    BVAnd,
    BVAShr,
    BVConcat,
    BVExtract,
    BVLShl,
    BVLShr,
    BVMul,
    BVNot,
    BVOr,
    BVSDiv,
    BVSRem,
    BVSub,
    BVUDiv,
    BVURem,
    BVXor,
    BVZExt,
    Equals,
    Ite,
    Not,
    NotEquals,
    Or,
    Symbol,
    simplify,
)
from pysmt.typing import BOOL, BVType, PySMTType

S = TypeVar("S")
T = TypeVar("T", bound="BitVector")
U = TypeVar("U", bound="Uint")
V = TypeVar("V", bound="Symbolic[Any]")


class Symbolic(abc.ABC, Generic[S]):
    """An SMT expression."""

    def __init__(self, arg: Union[str, FNode, S]) -> None:
        """Create a new Symbolic."""
        if isinstance(arg, str):
            self.node = Symbol(arg, self._pysmt_type())
        elif isinstance(arg, FNode):
            self.node = simplify(arg)
        else:
            self.node = self._pysmt_constant(arg)

    def __copy__(self: V) -> V:
        return self

    def __deepcopy__(self: V, memo: Any) -> V:
        return self

    @classmethod
    @abc.abstractmethod
    def _pysmt_type(cls) -> PySMTType:
        raise NotImplementedError

    @classmethod
    @abc.abstractmethod
    def _pysmt_constant(cls, arg: S) -> FNode:
        raise NotImplementedError


class BitVector(Symbolic[int]):
    """An SMT bitvector."""

    def __init__(self, arg: Union[str, FNode, int]):
        """Create a new BitVector."""
        if isinstance(arg, FNode):
            assert (
                arg.bv_width() == self.length()
            ), f"can't initialize {type(self).__name__} with {arg.bv_width()} bits"
        super().__init__(arg)

    @classmethod
    @abc.abstractmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        raise NotImplementedError

    @classmethod
    def _pysmt_type(cls) -> PySMTType:
        return BVType(cls.length())

    @classmethod
    def _pysmt_constant(cls, arg: int) -> FNode:
        assert isinstance(arg, int)
        assert arg >= 0, f"underflow: {arg} does not fit in {cls.__name__}"
        assert (
            arg < 2 ** cls.length()
        ), f"overflow: {arg} does not fit in {cls.__name__}"
        return BV(arg, cls.length())

    def __eq__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(Equals(self.node, other.node))

    def __ne__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(NotEquals(self.node, other.node))

    def __add__(self: T, other: T) -> T:
        return self.__class__(BVAdd(self.node, other.node))

    def __sub__(self: T, other: T) -> T:
        return self.__class__(BVSub(self.node, other.node))

    def __mul__(self: T, other: T) -> T:
        return self.__class__(BVMul(self.node, other.node))

    @overload
    def maybe_unwrap(self, into: Type[int] = int) -> Optional[int]:
        ...

    @overload
    def maybe_unwrap(self, into: Type[bytes]) -> Optional[bytes]:
        ...

    def maybe_unwrap(
        self, into: Union[Type[int], Type[bytes]] = int
    ) -> Optional[Union[int, bytes]]:
        """Return the bitvector's underlying value, if a constant."""
        if not self.node.is_constant():
            return None
        elif into == int:
            result = self.node.constant_value()
            assert isinstance(result, int)
            return result
        elif into == bytes:
            result = self.node.constant_value()
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
        into: Union[Type[int], Type[bytes]] = int,
        msg: str = "unexpected symbolic value",
    ) -> Union[int, bytes]:
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
    def _describe(cls, node: FNode) -> str:
        if node.is_constant():
            v = node.constant_value()
            if v < (1 << 256):
                return hex(v)
            p = []
            while v > 0:
                b = v & ((1 << 256) - 1)
                p.append(hex(b)[2:])
                v >>= 256
            return f"0x[{'.'.join(reversed(p))}]"
        else:
            digest = keccak.new(
                data=node.serialize().encode(), digest_bits=256
            ).digest()
            return "#" + digest[:3].hex()


class Uint(BitVector):
    """A bitvector representing an unsigned integer."""

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(BVULT(self.node, other.node))

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(BVULE(self.node, other.node))

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(BVUDiv(self.node, other.node))

    def __mod__(self: T, other: T) -> T:
        return self.__class__(BVURem(self.node, other.node))

    def __lshift__(self: T, other: T) -> T:
        return self.__class__(BVLShl(self.node, other.node))

    def __rshift__(self: T, other: T) -> T:
        return self.__class__(BVLShr(self.node, other.node))

    def __and__(self: T, other: T) -> T:
        return self.__class__(BVAnd(self.node, other.node))

    def __or__(self: T, other: T) -> T:
        return self.__class__(BVOr(self.node, other.node))

    def __xor__(self: T, other: T) -> T:
        return self.__class__(BVXor(self.node, other.node))

    def __invert__(self: T) -> T:
        return self.__class__(BVNot(self.node))

    def into(self, into: Type[U]) -> U:
        """Truncate or zero-extend the bitvector into a different type."""
        if into.length() > self.length():
            return into(BVZExt(self.node, into.length() - self.length()))
        else:
            return into(BVExtract(self.node, 0, into.length() - 1))


class Sint(BitVector):
    """A bitvector representing a signed integer."""

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(BVSLT(self.node, other.node))

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(BVSLE(self.node, other.node))

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(BVSDiv(self.node, other.node))

    def __mod__(self: T, other: T) -> T:
        return self.__class__(BVSRem(self.node, other.node))


class Uint8(Uint):
    """A uint8."""

    @classmethod
    def length(cls) -> Literal[8]:
        """Return the number of bits in the bitvector."""
        return 8


class Uint160(Uint):
    """A uint160."""

    @classmethod
    def length(cls) -> Literal[160]:
        """Return the number of bits in the bitvector."""
        return 160


class Uint256(Uint):
    """A uint256."""

    @classmethod
    def length(cls) -> Literal[256]:
        """Return the number of bits in the bitvector."""
        return 256

    @classmethod
    def from_bytes(cls, *args: Uint8) -> Uint256:
        """Create a new Uint256 from a list of 32 Uint8s."""
        assert len(args) == 32
        return Uint256(BVConcat(a.node for a in args))

    @classmethod
    def overflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a + b does not overflow."""
        result = a.into(Uint257) + b.into(Uint257)
        sign = BVExtract(result.node, 256, 256)
        return Constraint(Equals(sign, BV(0, 1)))

    @classmethod
    def underflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a - b does not underflow."""
        return a > b

    def as_signed(self) -> Sint256:
        """Reinterpret as a signed int256."""
        return Sint256(self.node)


class Uint257(Uint):
    """A uint257."""

    @classmethod
    def length(cls) -> Literal[257]:
        """Return the number of bits in the bitvector."""
        return 257


class Uint512(Uint):
    """A uint512."""

    @classmethod
    def length(cls) -> Literal[512]:
        """Return the number of bits in the bitvector."""
        return 512


class Sint256(Sint):
    """A signed int256."""

    @classmethod
    def length(cls) -> Literal[256]:
        """Return the number of bits in the bitvector."""
        return 256

    def as_unsigned(self) -> Uint256:
        """Reinterpret as an unsigned uint256."""
        return Uint256(self.node)

    def __lshift__(self: T, other: Uint256) -> T:
        return self.__class__(BVLShl(self.node, other.node))

    def __rshift__(self: T, other: Uint256) -> T:
        return self.__class__(BVAShr(self.node, other.node))


class Constraint(Symbolic[bool]):
    """A symbolic boolean value representing true or false."""

    def __init__(self, arg: Union[str, FNode, bool]):
        """Create a new Constraint."""
        if isinstance(arg, FNode):
            assert arg.get_type().is_bool_type()
        super().__init__(arg)

    @classmethod
    def _pysmt_type(cls) -> PySMTType:
        return BOOL

    @classmethod
    def _pysmt_constant(cls, arg: bool) -> FNode:
        assert isinstance(arg, bool)
        return Bool(arg)

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
        return Constraint(And(*(c.node for c in constraints)))

    @classmethod
    def any(cls, *constraints: Constraint) -> Constraint:
        """Return the OR of all given constraints."""
        return Constraint(Or(*(c.node for c in constraints)))

    def __invert__(self) -> Constraint:
        return Constraint(Not(self.node))

    def ite(self, then: V, else_: V) -> V:
        """Return a symbolic value: `then` if true, `else_` if false."""
        return then.__class__(Ite(self.node, then.node, else_.node))
