"""A pure-Python term-rewriting SMT frontend."""
# ruff: noqa

from __future__ import annotations

import abc
from functools import reduce
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

from smt2.rwbv import rewrite_bitvector
from smt2.rwcore import rewrite_constraint

from . import array, bv, core


class BitVectorMeta(abc.ABCMeta):
    _ccache: dict[str, type] = {}

    def __getitem__(self, N: Any, /) -> type:
        if isinstance(N, int):
            raise TypeError(
                f"integer passed to {self.__name__}[...]; use {self.__name__}[Literal[{N}]] instead"
            )

        if get_origin(N) != Literal:
            # No-op unbound type variables, unions, etc. These kind of Uint[...]
            # can be used in type signatures. Note that trying to instantiate
            # one will raise an error because width is not defined.
            return self

        args = get_args(N)
        if len(args) != 1 or not isinstance(args[0], int):
            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )

        n = args[0]
        if n <= 0:
            raise TypeError(f"{self.__name__} requires a positive width")

        name = self.__name__ + str(n)
        if name not in self._ccache:
            cls = type(name, (self,), {"width": n, "__slots__": ()})
            cls.__module__ = self.__module__
            self._ccache[name] = cls
        return self._ccache[name]


class Symbolic(abc.ABC):
    __slots__ = ("_term",)
    _term: core.Symbolic

    @classmethod
    def _apply(cls, op: type[core.Symbolic], *args: Symbolic) -> Self:
        k = cls.__new__(cls)
        k._term = op(*(a._term for a in args))
        if isinstance(k._term, core.Constraint):
            k._term = rewrite_constraint(k._term)
        elif isinstance(k._term, bv.BitVector):
            assert issubclass(cls, BitVector)
            k._term = rewrite_bitvector(k._term, cls.width)  # pyright: ignore
        return k

    # Implementation Note: Symbolic instances are immutable. For performance,
    # don't copy them.
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def __hash__(self) -> int:
        return self._term.__hash__()

    def __repr__(self) -> str:
        ctx = core.DumpContext()
        self._term.dump(ctx)
        return f"{self.__class__.__name__}({ctx.out.decode()})"


class Constraint(Symbolic):
    __slots__ = ()
    _term: core.Constraint

    def __init__(self, value: bool | str, /):
        match value:
            case bool():
                self._term = core.Value(value)
            case str():
                self._term = core.Symbol(value.encode())  # pyright: ignore[reportIncompatibleVariableOverride]

    def __invert__(self) -> Self:
        return self._apply(core.Not, self)

    def __and__(self, other: Self, /) -> Self:
        return self._apply(core.And, self, other)

    def __or__(self, other: Self, /) -> Self:
        return self._apply(core.Or, self, other)

    def __xor__(self, other: Self, /) -> Self:
        return self._apply(core.Xor, self, other)

    def __bool__(self) -> Never:
        raise TypeError("cannot use Constraint in a boolean context")

    @overload
    def ite[N: int](self, then: Uint[N], else_: Uint[N], /) -> Uint[N]: ...

    @overload
    def ite[N: int](self, then: Int[N], else_: Int[N], /) -> Int[N]: ...

    def ite[N: int](self, then: BitVector[N], else_: BitVector[N], /) -> BitVector[N]:
        assert then.width == else_.width
        return then._apply(bv.Ite, self, then, else_)

    def iff(self, other: Constraint) -> Constraint:
        return ~(self ^ other)

    def implies(self, other: Constraint) -> Constraint:
        return ~(self & ~other)

    def reveal(self) -> bool | None:
        match self._term:
            case core.Value(value):
                return value
            case _:
                return None


class BitVector[N: int](
    Symbolic, metaclass=abc.ABCMeta if TYPE_CHECKING else BitVectorMeta
):
    __slots__ = ()
    width: Final[N]  # pyright: ignore[reportGeneralTypeIssues]
    _term: bv.BitVector[N]

    def __init__(self, value: int | str, /) -> None:
        match value:
            case int():
                self._term = bv.Value(value, self.width)
            case str():
                self._term = bv.Symbol(value.encode(), self.width)  # pyright: ignore[reportIncompatibleVariableOverride]

    @abc.abstractmethod
    def __lt__(self, other: Self, /) -> Constraint: ...

    @abc.abstractmethod
    def __le__(self, other: Self, /) -> Constraint: ...

    def __invert__(self) -> Self:
        return self._apply(bv.Not, self)

    def __and__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.And, self, other)

    def __or__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Or, self, other)

    def __xor__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Xor, self, other)

    def __add__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Add, self, other)

    def __sub__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Sub, self, other)

    def __mul__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Mul, self, other)

    @abc.abstractmethod
    def __truediv__(self, other: Self, /) -> Self: ...

    @abc.abstractmethod
    def __mod__(self, other: Self, /) -> Self: ...

    def __lshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Shl, self, other)

    @abc.abstractmethod
    def __rshift__(self, other: Uint[N], /) -> Self: ...

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(core.Eq, self, other)

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._apply(core.Distinct, self, other)

    def __hash__(self) -> int:
        return self._term.__hash__()


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._apply(bv.Ult, self, other)

    def __le__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._apply(bv.Ule, self, other)

    def __truediv__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._apply(bv.Udiv, self, other)

    def __mod__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._apply(bv.Urem, self, other)

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Lshr, self, other)

    @overload
    def into[M: int](self: Uint[N], other: type[Int[N]], /) -> Int[N]: ...

    @overload
    def into[M: int](self: Uint[N], other: type[Uint[M]], /) -> Uint[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        k = other.__new__(other)
        if self.width == other.width:
            k._term = self._term  # pyright: ignore[reportAttributeAccessIssue]
        elif self.width < other.width:
            k._term = bv.ZeroExtend(other.width - self.width, self._term)
        else:
            k._term = bv.Extract(other.width - 1, 0, self._term)
        return k

    @classmethod
    def concat[M: int](cls, *terms: Uint[M]) -> Uint[N]:
        assert terms and cls.width == reduce(lambda s, t: s + t.width, terms, 0)
        k = cls.__new__(cls)
        k._term = bv.Concat(tuple(t._term for t in terms))  # pyright: ignore[reportPrivateUsage]
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
            case bv.Value(value):
                return value
            case _:
                return None


class Int[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._apply(bv.Sle, self, other)

    def __le__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        return Constraint._apply(bv.Sle, self, other)

    def __truediv__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._apply(bv.Sdiv, self, other)

    def __mod__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._apply(bv.Srem, self, other)

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._apply(bv.Ashr, self, other)

    @overload
    def into[M: int](self: Int[N], other: type[Uint[N]], /) -> Uint[N]: ...

    @overload
    def into[M: int](self: Int[N], other: type[Int[M]], /) -> Int[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        k = other.__new__(other)
        if self.width == other.width:
            k._term = self._term  # pyright: ignore[reportAttributeAccessIssue]
        elif self.width < other.width:
            k._term = bv.SignExtend(other.width - self.width, self._term)
        else:
            raise NotImplementedError("cannot truncate signed bitvector")
        return k

    def reveal(self) -> int | None:
        match self._term:
            case bv.Value(_):
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
    _term: array.Symbol[int, int] | array.Value[int, int] | array.Store[int, int]

    __hash__: ClassVar[None] = None  # pyright: ignore[reportIncompatibleMethodOverride]

    def __init__(self, value: V | str, /) -> None:
        width: tuple[int, int] = (self._key.width, self._value.width)
        match value:
            case BitVector():
                self._term = array.Value(value._term, *width)  # pyright: ignore[reportPrivateUsage]
            case str():
                self._term = array.Symbol(value.encode(), *width)

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise TypeError("arrays cannot be compared for equality.")

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise TypeError("arrays cannot be compared for equality.")

    def _mk_value(self, term: bv.BitVector[Any]) -> V:
        k = self._value.__new__(self._value)
        k._term = term  # pyright: ignore[reportPrivateUsage]
        return k

    def __getitem__(self, key: K) -> V:
        kterm = key._term  # pyright: ignore[reportPrivateUsage]
        match self._term:
            case array.Symbol():
                return self._value._apply(array.Select, self, key)
            case array.Value(default):
                return self._mk_value(default)
            case array.Store(default, lower, upper):
                if upper:
                    p, q = upper[0]
                    if kterm == p:
                        return self._mk_value(q)
                elif isinstance(kterm, bv.Value):
                    lower = dict(lower)
                    if kterm.value in lower:
                        return self._mk_value(lower[kterm.value])
                    elif isinstance(self._term, array.Symbol):
                        return self._value._apply(array.Select, self, key)
                    else:
                        return self._mk_value(self._term.default)  # pyright: ignore[reportArgumentType]
        return self._value._apply(array.Select, self, key)

    def __setitem__(self, key: K, value: V) -> None:
        match self._term:
            case array.Symbol() | array.Value():
                default = self._term
                lower, upper = {}, []
            case array.Store(default, lower, upper):
                lower, upper = dict(lower), list(upper)
        if upper or (k := key.reveal()) is None:
            upper.append((key._term, value._term))  # pyright: ignore[reportPrivateUsage]
        else:
            lower[k] = value._term  # pyright: ignore[reportPrivateUsage]
        self._term = array.Store(default, frozenset(lower.items()), tuple(upper))  # pyright: ignore[reportIncompatibleVariableOverride]
