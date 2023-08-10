"""Library for SMT solving."""

from __future__ import annotations

import abc
from typing import Any, Generic, Type, TypeVar

from Crypto.Hash import keccak
from pybitwuzla import BitwuzlaTerm, Kind

from .bitwuzla import cache, get_value_int, mk_bv_value, mk_const, mk_term, sort

S = TypeVar("S")

T = TypeVar("T", bound="BitVector")
U = TypeVar("U", bound="Uint")
V = TypeVar("V", bound="Symbolic[Any]")


class UniqueSymbolic(abc.ABCMeta):
    """A caching metaclass for Symbolic."""

    def __call__(cls, arg: Any) -> Any:  # type: ignore
        """Intercept calls to the Symbolic constructor."""
        if isinstance(arg, BitwuzlaTerm):
            # Don't try to hash BitwuzlaTerms
            return super().__call__(arg)
        c = cache()[cls]
        if not arg in c:
            c[arg] = super().__call__(arg)
        return c[arg]


class Symbolic(abc.ABC, Generic[S], metaclass=UniqueSymbolic):
    """An SMT expression."""

    __slots__ = ("node", "__weakref__")

    node: BitwuzlaTerm

    def __init__(self, arg: str | BitwuzlaTerm | S) -> None:
        """Create a new Symbolic."""
        ...

    def __copy__(self: V) -> V:
        return self

    def __deepcopy__(self: V, memo: Any) -> V:
        return self

    @abc.abstractmethod
    def is_constant_literal(self) -> bool:
        """Check if the expression has a concrete value."""
        ...

    def smtlib(self) -> str:
        """Output the symbolic expression as an SMT-LIBv2 formula."""
        return self.node.dump("smt2")


class BitVector(Symbolic[int]):
    """An SMT bitvector."""

    __slots__ = ()

    __hash__ = Symbolic.__hash__  # type: ignore

    def __init__(self, arg: str | BitwuzlaTerm | int):
        """Create a new BitVector."""
        match arg:
            case str():
                self.node = mk_const(sort(self.length()), arg)
            case BitwuzlaTerm():
                assert arg.is_bv()
                assert (
                    arg.get_sort().bv_get_size() == self.length()
                ), f"can't initialize {type(self).__name__} with {arg.get_sort().bv_get_size()} bits"
                self.node = arg
            case int():
                self.node = mk_bv_value(sort(self.length()), arg)

    @classmethod
    @abc.abstractmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        ...

    def __eq__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(mk_term(Kind.EQUAL, [self.node, other.node]))

    def __ne__(self: T, other: T) -> Constraint:  # type: ignore
        return Constraint(mk_term(Kind.DISTINCT, [self.node, other.node]))

    def __add__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_ADD, [self.node, other.node]))

    def __sub__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_SUB, [self.node, other.node]))

    def __mul__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_MUL, [self.node, other.node]))

    def is_constant_literal(self) -> bool:
        """Check if the bitvector has a concrete value."""
        result = self.node.is_bv_value()
        assert type(result) == bool
        return result

    def reveal(self) -> int | None:
        """Return the bitvector's underlying value, if a constant literal."""
        if not self.is_constant_literal():
            return None
        return get_value_int(self.node)

    def describe(self) -> str:
        """
        Produce a human-readable description of the given bitvector.

        For concrete bitvectors, returns a result in hexadecimal. Long values are
        broken into 256-bit chunks using dot syntax, e.g. "0x[1234.1]".

        For symbolic bitvectors, returns a hash based on the input variables.
        """
        return BitVector._describe(self.node)

    @classmethod
    def _describe(cls, node: BitwuzlaTerm) -> str:
        if node.is_bv_value():
            v = get_value_int(node)
            if v < (1 << 256):
                return hex(v)
            p: list[str] = []
            while v > 0:
                b = v & ((1 << 256) - 1)
                p.append(hex(b)[2:])
                v >>= 256
            return f"0x[{'.'.join(reversed(p))}]"
        else:
            digest = keccak.new(
                data=node.dump("smt2").encode(), digest_bits=256
            ).digest()
            return "#" + digest[:3].hex()


class Uint(BitVector):
    """A bitvector representing an unsigned integer."""

    __slots__ = ()

    def __hash__(self) -> int:
        return self.node.__hash__()

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(mk_term(Kind.BV_ULT, [self.node, other.node]))

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(mk_term(Kind.BV_ULE, [self.node, other.node]))

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_UDIV, [self.node, other.node]))

    def __mod__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_UREM, [self.node, other.node]))

    def __lshift__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_SHL, [self.node, other.node]))

    def __rshift__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_SHR, [self.node, other.node]))

    def __and__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_AND, [self.node, other.node]))

    def __or__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_OR, [self.node, other.node]))

    def __xor__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_XOR, [self.node, other.node]))

    def __invert__(self: T) -> T:
        return self.__class__(mk_term(Kind.BV_NOT, [self.node]))

    def into(self, into: Type[U]) -> U:
        """Truncate or zero-extend the bitvector into a different type."""
        if into.length() > self.length():
            return into(
                mk_term(
                    Kind.BV_ZERO_EXTEND,
                    [self.node],
                    [into.length() - self.length()],
                )
            )
        else:
            return into(mk_term(Kind.BV_EXTRACT, [self.node], [into.length() - 1, 0]))


class Sint(BitVector):
    """A bitvector representing a signed integer."""

    __slots__ = ()

    def __lt__(self: T, other: T) -> Constraint:
        return Constraint(mk_term(Kind.BV_SLT, [self.node, other.node]))

    def __le__(self: T, other: T) -> Constraint:
        return Constraint(mk_term(Kind.BV_SLE, [self.node, other.node]))

    def __floordiv__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_SDIV, [self.node, other.node]))

    def __mod__(self: T, other: T) -> T:
        return self.__class__(mk_term(Kind.BV_SREM, [self.node, other.node]))


class Uint8(Uint):
    """A uint8."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 8


class Uint160(Uint):
    """A uint160."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 160


class Uint256(Uint):
    """A uint256."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 256

    @classmethod
    def from_bytes(cls, *args: Uint8) -> Uint256:
        """Create a new Uint256 from a list of 32 Uint8s."""
        assert len(args) == 32
        return Uint256(mk_term(Kind.BV_CONCAT, [a.node for a in args]))

    @classmethod
    def overflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a + b does not overflow."""
        cond = mk_term(Kind.BV_UADD_OVERFLOW, [a.node, b.node])
        return Constraint(mk_term(Kind.NOT, [cond]))

    @classmethod
    def underflow_safe(cls, a: Uint256, b: Uint256) -> Constraint:
        """Return a constraint asserting that a - b does not underflow."""
        cond = mk_term(Kind.BV_USUB_OVERFLOW, [a.node, b.node])
        return Constraint(mk_term(Kind.NOT, [cond]))

    def as_signed(self) -> Sint256:
        """Reinterpret as a signed int256."""
        return Sint256(self.node)


class Sint256(Sint):
    """A signed int256."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 256

    def as_unsigned(self) -> Uint256:
        """Reinterpret as an unsigned uint256."""
        return Uint256(self.node)

    def __lshift__(self: T, other: Uint256) -> T:
        return self.__class__(mk_term(Kind.BV_SHL, [self.node, other.node]))

    def __rshift__(self: T, other: Uint256) -> T:
        return self.__class__(mk_term(Kind.BV_ASHR, [self.node, other.node]))


class Uint257(Uint):
    """A uint257."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 257


class Uint512(Uint):
    """A uint512."""

    __slots__ = ()

    @classmethod
    def length(cls) -> int:
        """Return the number of bits in the bitvector."""
        return 512


class Constraint(Symbolic[bool]):
    """A symbolic boolean value representing true or false."""

    __slots__ = ()

    def __init__(self, arg: str | BitwuzlaTerm | bool):
        """Create a new Constraint."""
        if isinstance(arg, str):
            self.node = mk_const(sort(1), arg)
        elif isinstance(arg, BitwuzlaTerm):
            assert arg.is_bv()
            assert arg.get_sort().bv_get_size() == 1
            self.node = arg
        elif type(arg) == bool:
            self.node = mk_bv_value(sort(1), int(arg))
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
        if len(constraints) == 0:
            return Constraint(False)
        result = constraints[0].node
        for constraint in constraints[1:]:
            result = mk_term(Kind.AND, [result, constraint.node])
        return Constraint(result)

    @classmethod
    def any(cls, *constraints: Constraint) -> Constraint:
        """Return the OR of all given constraints."""
        if len(constraints) == 0:
            return Constraint(False)
        result = constraints[0].node
        for constraint in constraints[1:]:
            result = mk_term(Kind.OR, [result, constraint.node])
        return Constraint(result)

    def __invert__(self) -> Constraint:
        return Constraint(mk_term(Kind.NOT, [self.node]))

    def ite(self, then: V, else_: V) -> V:
        """Return a symbolic value: `then` if true, `else_` if false."""
        return then.__class__(mk_term(Kind.ITE, [self.node, then.node, else_.node]))

    def is_constant_literal(self) -> bool:
        """Check if the constraint has a concrete value."""
        result = self.node.is_bv_value()
        assert type(result) == bool
        return result

    def reveal(self) -> bool | None:
        """Return the constraint's underlying value, if a constant literal."""
        result = self.node.dump("smt2")
        if result == "true":
            return True
        elif result == "false":
            return False
        else:
            return None
