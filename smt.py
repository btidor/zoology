"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass
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


class BitVectorMeta(abc.ABCMeta):
    _ccache: dict[str, type] = {}

    def __getitem__(self, N: Any, /) -> Any:
        if isinstance(N, int):
            raise TypeError(
                f"integer passed to {self.__name__}[...]; use {self.__name__}[Literal[{N}]] instead"
            )

        if get_origin(N) != Literal:
            # No-op unbound type variables, unions, etc. These kind of Uint[...]
            # can be used in type signatures. Note that trying to instantiate
            # one will raise an error because _sort is not defined.
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
            if hasattr(a, "_sort"):
                continue  # `a` is a usable BitVector

            if get_origin(a) is Union or isinstance(a, TypeVar):
                # No-op unbound type variables, unions, etc. These kind of
                # Array[...] can be used in type signatures. Note that trying to
                # instantiate one will raise an error because _sort is not
                # defined.
                return self

            if isinstance(a, BitVectorMeta):
                # Partially-specified BitVector, e.g. Int[Union[...]]; handle
                # the same as above.
                return self

            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )

        name = self.__name__ + "[" + k.__name__ + ", " + v.__name__ + "]"
        if name not in self._ccache:
            sort = cast(Any, self)._make_sort(k, v)
            cls = type(
                name, (self,), {"_sort": sort, "_key": k, "_value": v, "__slots__": ()}
            )
            cls.__module__ = self.__module__
            self._ccache[name] = cls
        return self._ccache[name]


class Symbolic(abc.ABC):
    __slots__ = ("_term",)
    _term: BooleanTerm | BitvectorTerm

    @classmethod
    def _from_term(cls, term: Any, /) -> Self:
        k = cls.__new__(cls)
        k._term = term
        return k

    # Implementation Note: Symbolic instances are immutable. For performance,
    # don't copy them.
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def __hash__(self) -> int:
        return self._term.__hash__()


type BooleanTerm = bool | str | NotOp | AndOp | OrOp | XorOp | BvEqOp


@dataclass(frozen=True, slots=True)
class NotOp:
    arg: BooleanTerm

    @classmethod
    def apply(cls, term: BooleanTerm) -> BooleanTerm:
        match term:
            case bool():
                return not term
            case NotOp(arg):  # double negation
                return arg
            case _:
                return NotOp(term)


@dataclass(frozen=True, slots=True)
class AndOp:
    args: set[BooleanTerm]

    @classmethod
    def apply(cls, *terms: BooleanTerm) -> BooleanTerm:
        args = set[BooleanTerm]()
        for term in terms:
            match term:
                case True:
                    pass
                case False:
                    return False
                case AndOp():
                    args.intersection_update(term.args)  # A & A => A
                case _:
                    args.add(term)
        return AndOp(args) if args else True


@dataclass(frozen=True, slots=True)
class OrOp:
    args: set[BooleanTerm]

    @classmethod
    def apply(cls, *terms: BooleanTerm) -> BooleanTerm:
        args = set[BooleanTerm]()
        for term in terms:
            match term:
                case True:
                    return True
                case False:
                    pass
                case OrOp():
                    args.intersection_update(term.args)  # A | A => A
                case _:
                    args.add(term)
        return OrOp(args) if args else False


@dataclass(frozen=True, slots=True)
class XorOp:
    base: bool
    args: set[BooleanTerm]

    @classmethod
    def apply(cls, *terms: BooleanTerm) -> BooleanTerm:
        invert = False  # False ^ X => X / True ^ X => ~X
        args = set[BooleanTerm]()
        deferred = set[NotOp]()
        queue = list(terms)
        while queue:
            match term := queue.pop():
                case bool():
                    invert ^= term
                case XorOp():
                    queue.extend(term.args)
                case NotOp():
                    if term in deferred:  # A ^ A => False
                        deferred.remove(term)
                        invert ^= False
                    else:
                        deferred.add(term)
                case _:
                    if term in args:  # A ^ A => False
                        args.remove(term)
                        invert ^= False
                    else:
                        args.add(term)
        for d in deferred:
            if d.arg in args:  # A ^ ~A => True
                assert not isinstance(d.arg, XorOp)
                args.remove(d.arg)
                invert ^= True
            else:
                args.add(d)
        return XorOp(invert, args) if args else invert


class Constraint(Symbolic):
    __slots__ = ()
    _term: BooleanTerm

    def __init__(self, value: bool | str, /):
        self._term = value  # pyright: ignore

    def __invert__(self) -> Self:
        return self._from_term(NotOp.apply(self._term))

    def __and__(self, other: Self, /) -> Self:
        return self._from_term(AndOp.apply(self._term, other._term))

    def __or__(self, other: Self, /) -> Self:
        return self._from_term(OrOp.apply(self._term, other._term))

    def __xor__(self, other: Self, /) -> Self:
        return self._from_term(XorOp.apply(self._term, other._term))

    def __bool__(self) -> Never:
        raise TypeError("cannot use Constraint in a boolean context")

    @overload
    def ite[N: int](self, then: Uint[N], else_: Uint[N], /) -> Uint[N]: ...

    @overload
    def ite[N: int](self, then: Int[N], else_: Int[N], /) -> Int[N]: ...

    def ite[N: int](self, then: BitVector[N], else_: BitVector[N], /) -> BitVector[N]:
        match self._term:
            case True:
                return then
            case False:
                return else_
            case _:
                raise NotImplementedError

    def reveal(self) -> bool | None:
        return self._term if isinstance(self._term, bool) else None


type BitvectorTerm = int | str | BvNotOp | BvAndOp | BvOrOp | BvArithOp


@dataclass(frozen=True, slots=True)
class BvNotOp:
    arg: BitvectorTerm

    @classmethod
    def apply(cls, width: int, term: BitvectorTerm) -> BitvectorTerm:
        mask = (1 << width) - 1
        match term:
            case int():
                return mask ^ term
            case BvNotOp(arg):  # double negation
                return arg
            case str() | BvAndOp() | BvOrOp() | BvArithOp():
                return BvNotOp(term)


@dataclass(frozen=True, slots=True)
class BvAndOp:
    mask: int
    args: set[BitvectorTerm]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        mask = (1 << width) - 1
        args = set[BitvectorTerm]()
        deferred = set[BvNotOp]()
        for term in terms:
            match term:
                case int():
                    mask &= term
                case BvAndOp():
                    mask &= term.mask
                    args.intersection_update(term.args)  # A & A => A
                case BvNotOp():
                    deferred.add(term)
                case str() | BvOrOp() | BvArithOp():
                    args.add(term)
        for term in deferred:
            if term.arg in args:
                return 0  # A & ~A => 0
            else:
                args.add(term)
        if mask == (1 << width) - 1:  # 0xFF & A => 0xFF
            return mask
        return BvAndOp(mask, args) if args else mask


@dataclass(frozen=True, slots=True)
class BvOrOp:
    mask: int
    args: set[BitvectorTerm]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        mask = 0
        args = set[BitvectorTerm]()
        deferred = set[BvNotOp]()
        for term in terms:
            match term:
                case int():
                    mask |= term
                case BvOrOp():
                    mask |= term.mask
                    args.intersection_update(term.args)  # A | A => A
                case BvNotOp():
                    deferred.add(term)
                case str() | BvAndOp() | BvArithOp():
                    args.add(term)
        for term in deferred:
            if term.arg in args:
                return (1 << width) - 1  # A | ~A => 0xFF
            else:
                args.add(term)
        if mask == 0:  # 0 | A => 0
            return mask
        return BvOrOp(mask, args) if args else mask


@dataclass(frozen=True, slots=True)
class BvArithOp:
    base: int
    args: tuple[BitvectorTerm, ...]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        base = 0
        limit = 1 << width
        args = list[BitvectorTerm]()
        deferred = list[BvNotOp]()
        for term in terms:
            match term:
                case int():
                    base = (base + term) % limit
                case BvArithOp():
                    base = (base + term.base) % limit
                    args.extend(term.args)
                case BvNotOp():
                    deferred.append(term)
                case str() | BvAndOp() | BvOrOp():
                    args.append(term)
        for term in deferred:
            if term.arg in args:  # A + ~A => 0xFF
                args.remove(term.arg)
                base = (base + limit - 1) % limit
            else:
                args.append(term)
        return BvArithOp(base, tuple(args)) if args else base


@dataclass(frozen=True, slots=True)
class BvEqOp:
    left: BitvectorTerm
    right: BitvectorTerm

    @classmethod
    def apply(cls, left: BitvectorTerm, right: BitvectorTerm) -> BooleanTerm:
        match (left, right):
            case int(), int():
                return left == right
            case _:
                return BvEqOp(left, right)


class BitVector[N: int](
    Symbolic, metaclass=abc.ABCMeta if TYPE_CHECKING else BitVectorMeta
):
    __slots__ = ()
    width: Final[int]  # pyright: ignore
    _term: BitvectorTerm

    def __init__(self, value: int | str, /) -> None:
        self._term = value  # pyright: ignore

    @abc.abstractmethod
    def __lt__(self, other: Self, /) -> Constraint: ...

    @abc.abstractmethod
    def __le__(self, other: Self, /) -> Constraint: ...

    def __invert__(self) -> Self:
        return self._from_term(BvNotOp.apply(self.width, self._term))

    def __and__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(BvAndOp.apply(self.width, self._term, other._term))

    def __or__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(BvOrOp.apply(self.width, self._term, other._term))

    def __xor__(self, other: Self, /) -> Self:
        assert self.width == other.width
        raise NotImplementedError

    def __add__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(BvArithOp.apply(self.width, self._term, other._term))

    def __sub__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvArithOp.apply(
                self.width, self._term, BvNotOp.apply(self.width, other._term), 1
            )
        )

    def __mul__(self, other: Self, /) -> Self:
        raise NotImplementedError

    @abc.abstractmethod
    def __truediv__(self, other: Self, /) -> Self: ...

    @abc.abstractmethod
    def __mod__(self, other: Self, /) -> Self: ...

    def __lshift__(self, other: Uint[N], /) -> Self:
        raise NotImplementedError

    @abc.abstractmethod
    def __rshift__(self, other: Uint[N], /) -> Self: ...

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(BvEqOp.apply(self._term, other._term))

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(NotOp.apply(BvEqOp.apply(self._term, other._term)))

    def __hash__(self) -> int:
        return self._term.__hash__()


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        raise NotImplementedError

    def __le__(self, other: Self, /) -> Constraint:
        raise NotImplementedError

    def __truediv__(self, other: Self, /) -> Self:
        raise NotImplementedError

    def __mod__(self, other: Self, /) -> Self:
        raise NotImplementedError

    def __rshift__(self, other: Uint[N], /) -> Self:
        raise NotImplementedError

    @overload
    def into[M: int](self: Uint[N], other: type[Int[N]], /) -> Int[N]: ...

    @overload
    def into[M: int](self: Uint[N], other: type[Uint[M]], /) -> Uint[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        raise NotImplementedError

    def reveal(self) -> int | None:
        return self._term if isinstance(self._term, int) else None


class Int[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        raise NotImplementedError

    def __le__(self, other: Self, /) -> Constraint:
        raise NotImplementedError

    def __truediv__(self, other: Self, /) -> Self:
        raise NotImplementedError

    def __mod__(self, other: Self, /) -> Self:
        raise NotImplementedError

    def __rshift__(self, other: Uint[N], /) -> Self:
        raise NotImplementedError

    @overload
    def into[M: int](self: Int[N], other: type[Uint[N]], /) -> Uint[N]: ...

    @overload
    def into[M: int](self: Int[N], other: type[Int[M]], /) -> Int[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        raise NotImplementedError

    def reveal(self) -> int | None:
        raise NotImplementedError


class Array[K: Uint[Any] | Int[Any], V: Uint[Any] | Int[Any]](
    metaclass=type if TYPE_CHECKING else ArrayMeta
):
    __slots__ = ("_term",)
    __hash__: ClassVar[None] = None  # pyright: ignore[reportIncompatibleMethodOverride]

    def __init__(self, value: V | str, /) -> None:
        self._term = value

    def __copy__(self) -> Self:
        raise NotImplementedError

    def __deepcopy__(self, memo: Any, /) -> Self:
        raise NotImplementedError

    def __repr__(self) -> str:
        raise NotImplementedError

    # Implementation Note: Arrays cannot be compared for equality.
    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise NotImplementedError

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise NotImplementedError

    def __getitem__(self, key: K) -> V:
        raise NotImplementedError

    def __setitem__(self, key: K, value: V) -> None:
        raise NotImplementedError


class Solver:
    constraint: Constraint

    def __init__(self) -> None:
        raise NotImplementedError

    def add(self, assertion: Constraint, /) -> None:
        raise NotImplementedError

    def check(self, *assumptions: Constraint) -> bool:
        raise NotImplementedError

    @overload
    def evaluate(self, s: Constraint, /) -> bool: ...

    @overload
    def evaluate[N: int](self, s: Uint[N] | Int[N], /) -> int: ...

    @overload
    def evaluate[N: int, M: int](
        self, s: Array[Uint[N], Uint[M]], /
    ) -> dict[int, int]: ...

    def evaluate[N: int, M: int](
        self, s: Constraint | Uint[N] | Int[N] | Array[Uint[N], Uint[M]], /
    ) -> bool | int | dict[int, int]:
        raise NotImplementedError


Uint8 = Uint[Literal[8]]
Uint64 = Uint[Literal[64]]
Uint128 = Uint[Literal[128]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

Int256 = Int[Literal[256]]


class NarrowingError(Exception):
    pass


class ConstrainingError(Exception):
    pass


def describe[N: int](s: Uint[N]) -> str:
    raise NotImplementedError


def overflow_safe[N: int](a: Uint[N], b: Uint[N]) -> Constraint:
    raise NotImplementedError


def underflow_safe[N: int](a: Uint[N], b: Uint[N]) -> Constraint:
    raise NotImplementedError


def compact_array[N: int, M: int](
    solver: Solver, constraint: Constraint, a: Array[Uint[N], Uint[M]]
) -> Constraint:
    raise NotImplementedError


def compact_helper[N: int](
    solver: Solver, constraint: Constraint, a: Uint[N], b: Uint[N]
) -> tuple[Constraint, Uint[N]]:
    raise NotImplementedError


def concat_bytes(*bytes: Uint8) -> Uint[Any]:
    raise NotImplementedError


def concat_words(*words: Uint256) -> Uint[Any]:
    raise NotImplementedError


def explode_bytes(v: Uint256) -> list[Uint8]:
    raise NotImplementedError


def smart_arith[N: int](v: Uint[N]) -> tuple[Uint[N], int]:
    raise NotImplementedError


def smart_cmp(v: Constraint) -> bool | None:
    raise NotImplementedError


def iff(a: Constraint, b: Constraint) -> Constraint:
    raise NotImplementedError


def implies(a: Constraint, b: Constraint) -> Constraint:
    raise NotImplementedError


def prequal[N: int](a: Uint[N], b: Uint[N]) -> bool:
    raise NotImplementedError


def bvlshr_harder[N: int](a: Uint[N], b: Uint[N]) -> Uint[N]:
    raise NotImplementedError


def get_constants[N: int](v: Constraint | Uint[N] | Int[N]) -> Any:
    raise NotImplementedError


def substitute(s: Symbolic, b: Any) -> Any:
    raise NotImplementedError


def substitute2[N: int](s: Uint[N], b: Any) -> Uint[N]:
    raise NotImplementedError
