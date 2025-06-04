"""A pure-Python term-rewriting SMT frontend."""
# ruff: noqa: D101, D102, D103, D107

from __future__ import annotations

import abc
from typing import (
    TYPE_CHECKING,
    Any,
    ClassVar,
    Final,
    Literal,
    Never,
    Self,
    TypeVar,
    Union,
    cast,
    get_args,
    get_origin,
    overload,
)

from .composite import (
    Add,
    And,
    Ashr,
    ASymbol,
    AValue,
    BAnd,
    BNot,
    BOr,
    BSymbol,
    BValue,
    BXor,
    Concat,
    CSymbol,
    CValue,
    Distinct,
    Eq,
    Extract,
    Ite,
    Lshr,
    Mul,
    Not,
    Or,
    Sdiv,
    Select,
    Shl,
    SignExtend,
    Sle,
    Slt,
    Srem,
    Store,
    Sub,
    Udiv,
    Ule,
    Ult,
    Urem,
    Xor,
    ZeroExtend,
)
from .composite import BitVector as BitVectorTerm
from .composite import Constraint as ConstraintTerm
from .theory_core import Base as CoreSymbolic
from .theory_core import DumpContext

# pyright: reportIncompatibleMethodOverride=false
# pyright: reportIncompatibleVariableOverride=false


class BitVectorMeta(abc.ABCMeta):
    _ccache: dict[str, type] = {}

    def __getitem__(self, N: Any, /) -> type:
        if isinstance(N, int):
            n = N
        elif get_origin(N) != Literal:
            # No-op unbound type variables, unions, etc. These kind of Uint[...]
            # can be used in type signatures. Note that trying to instantiate
            # one will raise an error because width is not defined.
            return self
        elif len(args := get_args(N)) != 1 or not isinstance(args[0], int):
            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )
        elif (n := args[0]) <= 0:
            raise TypeError(f"{self.__name__} requires a positive width")

        name = self.__name__ + str(n)
        if name not in self._ccache:
            cls = type(name, (self,), {"width": n, "__slots__": ()})
            cls.__module__ = self.__module__
            self._ccache[name] = cls
        return self._ccache[name]


class Symbolic(abc.ABC):
    __slots__ = ("_term",)
    _term: CoreSymbolic

    @classmethod
    def _apply(cls, op: type[CoreSymbolic], *args: Symbolic) -> Self:
        k = cls.__new__(cls)
        k._term = op(*(a._term for a in args))
        return k

    # Implementation Note: Symbolic instances (except Arrays) are immutable. For
    # performance, don't copy them.
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def __hash__(self) -> int:
        return self._term.__hash__()

    def __repr__(self) -> str:
        ctx = DumpContext()
        self._term.dump(ctx)
        return f"{self.__class__.__name__}({ctx.out.decode()})"


class Constraint(Symbolic):
    __slots__ = ()
    _term: ConstraintTerm

    def __init__(self, value: bool | str, /):
        match value:
            case bool():
                self._term = CValue(value)
            case str():
                self._term = CSymbol(value.encode())

    def __invert__(self) -> Self:
        return self._apply(Not, self)

    def __and__(self, other: Self, /) -> Self:
        return self._apply(And, self, other)

    def __or__(self, other: Self, /) -> Self:
        return self._apply(Or, self, other)

    def __xor__(self, other: Self, /) -> Self:
        return self._apply(Xor, self, other)

    def __bool__(self) -> Never:
        raise TypeError("cannot use Constraint in a boolean context")

    @overload
    def ite[N: int](self, then: Uint[N], else_: Uint[N], /) -> Uint[N]: ...

    @overload
    def ite[N: int](self, then: Int[N], else_: Int[N], /) -> Int[N]: ...

    def ite[N: int](self, then: BitVector[N], else_: BitVector[N], /) -> BitVector[N]:
        assert then.width == else_.width
        return then._apply(Ite, self, then, else_)

    def iff(self, other: Constraint) -> Constraint:
        return ~(self ^ other)

    def implies(self, other: Constraint) -> Constraint:
        return ~(self & ~other)

    def reveal(self) -> bool | None:
        match self._term:
            case CValue(value):
                return value
            case _:
                return None


class BitVector[N: int](
    Symbolic, metaclass=abc.ABCMeta if TYPE_CHECKING else BitVectorMeta
):
    __slots__ = ()
    width: Final[N]  # pyright: ignore[reportGeneralTypeIssues]
    _term: BitVectorTerm

    def __init__(self, value: int | str, /) -> None:
        match value:
            case int():
                self._term = BValue(value, self.width)
            case str():
                self._term = BSymbol(value.encode(), self.width)

    @abc.abstractmethod
    def __lt__(self, other: Self, /) -> Constraint: ...

    @abc.abstractmethod
    def __le__(self, other: Self, /) -> Constraint: ...

    def __invert__(self) -> Self:
        return self._apply(BNot, self)

    def __and__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(BAnd, self, other)

    def __or__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(BOr, self, other)

    def __xor__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(BXor, self, other)

    def __add__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Add, self, other)

    def __sub__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Sub, self, other)

    def __mul__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Mul, self, other)

    @abc.abstractmethod
    def __truediv__(self, other: Self, /) -> Self: ...

    @abc.abstractmethod
    def __mod__(self, other: Self, /) -> Self: ...

    def __lshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(Shl, self, other)

    @abc.abstractmethod
    def __rshift__(self, other: Uint[N], /) -> Self: ...

    def __eq__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(Eq, self, other)

    def __ne__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(Distinct, self, other)

    def __hash__(self) -> int:
        return self._term.__hash__()


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(Ult, self, other)

    def __le__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(Ule, self, other)

    def __truediv__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Udiv, self, other)

    def __mod__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Urem, self, other)

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(Lshr, self, other)

    @overload
    def into[M: int](self: Uint[N], other: type[Int[N]], /) -> Int[N]: ...

    @overload
    def into[M: int](self: Uint[N], other: type[Uint[M]], /) -> Uint[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        k = other.__new__(other)
        if self.width == other.width:
            k._term = self._term
        elif self.width < other.width:
            k._term = ZeroExtend(other.width - self.width, self._term)
        else:
            k._term = Extract(other.width - 1, 0, self._term)
        return k

    @classmethod
    def concat[M: int](cls, *terms: Uint[M]) -> Uint[N]:
        k = cls.__new__(cls)
        k._term = Concat(tuple(t._term for t in terms))
        assert k.width == cls.width
        return k

    @classmethod
    def explode(cls, v: Uint[Any]) -> list[Uint[N]]:
        assert v.width % cls.width == 0
        r = list[Uint[N]]()
        shift = v.__class__(cls.width)
        for _ in range(32):
            r.append(v.into(cls))
            v >>= shift
        return r

    def reveal(self) -> int | None:
        match self._term:
            case BValue(value):
                return value
            case _:
                return None


class Int[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(Slt, self, other)

    def __le__(self, other: Self, /) -> Constraint:
        return Constraint._apply(Sle, self, other)

    def __truediv__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Sdiv, self, other)

    def __mod__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(Srem, self, other)

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(Ashr, self, other)

    @overload
    def into[M: int](self: Int[N], other: type[Uint[N]], /) -> Uint[N]: ...

    @overload
    def into[M: int](self: Int[N], other: type[Int[M]], /) -> Int[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        k = other.__new__(other)
        if self.width == other.width:
            k._term = self._term
        elif self.width < other.width:
            k._term = SignExtend(other.width - self.width, self._term)
        else:
            raise NotImplementedError("cannot truncate signed bitvector")
        return k

    def reveal(self) -> int | None:
        match self._term:
            case BValue(_):
                raise NotImplementedError
            case _:
                return None


class ArrayMeta(abc.ABCMeta):
    _ccache: dict[str, type] = {}

    def __getitem__(self, args: Any, /) -> Any:
        if (
            not isinstance(args, tuple) or len(args) != 2  # pyright: ignore[reportUnknownArgumentType]
        ):
            raise TypeError(
                f"unexpected type parameter passed to {self.__name__}[...]; expected a pair of types"
            )

        k, v = cast("tuple[Any, Any]", args)
        for a in (k, v):
            if hasattr(a, "width"):
                continue  # `a` is a usable BitVector

            if get_origin(a) is Union or isinstance(a, TypeVar):
                # No-op unbound type variables, unions, etc. These kind of
                # Array[...] can be used in type signatures. Note that trying to
                # instantiate one will raise an error because width is not
                # defined.
                return self

            if isinstance(a, BitVectorMeta):
                # Partially-specified BitVector, e.g. Int[Union[...]]; handle
                # the same as above.
                return self

            if a == Any:
                return self

            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )

        name = self.__name__ + "[" + k.__name__ + ", " + v.__name__ + "]"
        if name not in self._ccache:
            cls = type(name, (self,), {"_key": k, "_value": v, "__slots__": ()})
            cls.__module__ = self.__module__
            self._ccache[name] = cls
        return self._ccache[name]


class Array[K: Uint[Any] | Int[Any], V: Uint[Any] | Int[Any]](
    Symbolic, metaclass=type if TYPE_CHECKING else ArrayMeta
):
    __slots__ = ()

    _key: Final[type[K]]  # pyright: ignore[reportGeneralTypeIssues]
    _value: Final[type[V]]  # pyright: ignore[reportGeneralTypeIssues]
    _term: ASymbol | AValue | Store

    __hash__: ClassVar[None] = None

    def __init__(self, value: V | str, /) -> None:
        match value:
            case BitVector():
                self._term = AValue(value._term, self._key.width)  # pyright: ignore[reportPrivateUsage]
            case str():
                self._term = ASymbol(value.encode(), self._key.width, self._value.width)

    def __eq__(self, other: Never, /) -> Never:
        raise TypeError("Array cannot be compared for equality.")

    def __ne__(self, other: Never, /) -> Never:
        raise TypeError("Array cannot be compared for equality.")

    def __copy__(self) -> Self:
        k = self.__class__.__new__(self.__class__)
        k._term = self._term
        return k

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self.__copy__()

    def _mk_value(self, term: BitVectorTerm) -> V:
        k = self._value.__new__(self._value)
        k._term = term  # pyright: ignore[reportPrivateUsage]
        return k

    def __getitem__(self, key: K) -> V:
        kterm = key._term  # pyright: ignore[reportPrivateUsage]
        match self._term:
            case ASymbol():
                return self._value._apply(Select, self, key)
            case AValue(default):
                return self._mk_value(default)
            case Store(default, lower, upper):
                if upper:
                    p, q = upper[0]
                    if kterm == p:
                        return self._mk_value(q)
                elif isinstance(kterm, BValue):
                    lower = dict(lower)
                    if kterm.value in lower:
                        return self._mk_value(lower[kterm.value])
                    else:
                        if isinstance(self._term.base, ASymbol):
                            return self._mk_value(Select(self._term.base, kterm))
                        else:
                            return self._mk_value(self._term.base.default)
        return self._value._apply(Select, self, key)

    def __setitem__(self, key: K, value: V) -> None:
        match self._term:
            case ASymbol() | AValue():
                default = self._term
                lower, upper = {}, []
            case Store(default, lower, upper):
                lower, upper = dict(lower), list(upper)
        if upper or (k := key.reveal()) is None:
            upper.append((key._term, value._term))  # pyright: ignore[reportPrivateUsage]
        else:
            lower[k] = value._term  # pyright: ignore[reportPrivateUsage]
        self._term = Store(default, frozenset(lower.items()), tuple(upper))
