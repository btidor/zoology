"""Definitions and rewrite rules for the theory of bitvectors."""
# ruff: noqa

from __future__ import annotations
import abc
from typing import TYPE_CHECKING, Any, Final, Literal, get_args, get_origin

from ._base import DumpContext, Symbolic
from ._constraint import Constraint


class Meta(abc.ABCMeta):
    _cache: dict[str, type[BitVector[Any]]] = {}

    def __call__(cls, *args: Any) -> BitVector[int]:
        if issubclass(cls, BitVector) and not issubclass(cls, Placeholder):
            W: Any = Literal[cls.width]
            match args:
                case (int() as i,):
                    return Value[W](i)
                case (str() as s,):
                    return Symbol[W](s)
                case _:
                    raise TypeError(f"cannot init BitVector with args: {args}")
        else:
            return super().__call__(*args)

    def __getitem__(self, N: Any, /) -> Any:
        if isinstance(N, int):  # e.g. Uint[8]
            raise TypeError(
                f"integer passed to {self.__name__}[...]; use {self.__name__}[Literal[{N}]] instead"
            )
        elif get_origin(N) != Literal:  # N = TypeVar("N"); Uint[N]
            return self
        elif len(args := get_args(N)) != 1 or not isinstance(args[0], int):
            # Uint[Literal[1, 2]], Uint[Literal["A"]], etc.
            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )
        elif (n := args[0]) <= 0:  # Uint[Literal[-1]]
            raise TypeError(f"{self.__name__} requires a positive width")
        elif (name := self.__name__ + str(n)) not in self._cache:
            cls: Any = type(name, (self,), {"width": n, "__slots__": ()})
            cls.__module__ = self.__module__
            self._cache[name] = cls
        return self._cache[name]


# This prevents the metaclass from breaking __init__() type checking:
TMeta = abc.ABCMeta if TYPE_CHECKING else Meta


class BitVector[N: int](Symbolic, metaclass=TMeta):
    __slots__ = ()
    width: Final[int]  # pyright: ignore[reportGeneralTypeIssues]

    def __init__(self, value: int | str, /) -> None:
        raise TypeError("__init__ should be handled by metaclass")

    @abc.abstractmethod
    def __repr__(self) -> str: ...

    @abc.abstractmethod
    def __lt__(self, other: BitVector[N], /) -> Constraint: ...

    @abc.abstractmethod
    def __le__(self, other: BitVector[N], /) -> Constraint: ...

    def __invert__(self) -> BitVector[N]:
        return rewrite(Not(self))

    def __and__(self, other: BitVector[N], /) -> BitVector[N]:
        return rewrite(And(self, other))

    def __or__(self, other: BitVector[N], /) -> BitVector[N]:
        return rewrite(Or(self, other))

    def __xor__(self, other: BitVector[N], /) -> BitVector[N]:
        return rewrite(Xor(self, other))

    def __add__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

    def __sub__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

    def __mul__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

    @abc.abstractmethod
    def __truediv__(self, other: BitVector[N], /) -> BitVector[N]: ...

    @abc.abstractmethod
    def __mod__(self, other: BitVector[N], /) -> BitVector[N]: ...

    def __lshift__(self, other: Uint[N], /) -> BitVector[N]:
        raise NotImplementedError

    @abc.abstractmethod
    def __rshift__(self, other: Uint[N], /) -> BitVector[N]: ...

    # def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
    #     self, other: BitVector[N], /
    # ) -> Constraint:
    #     raise NotImplementedError

    # def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
    #     self, other: BitVector[N], /
    # ) -> Constraint:
    #     raise NotImplementedError

    def reveal(self) -> int | None:
        return None


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __repr__(self) -> str:
        ctx = DumpContext()
        self._dump(ctx)
        return f"Uint{self.width}({ctx.out.decode()})"

    def __lt__(self, other: Uint[N], /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __le__(self, other: Uint[N], /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __truediv__(self, other: Uint[N], /) -> Uint[N]:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __mod__(self, other: Uint[N], /) -> Uint[N]:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __rshift__(self, other: Uint[N], /) -> Uint[N]:
        raise NotImplementedError

    # TODO: into()


class Int[N: int](BitVector[N]):
    __slots__ = ()

    def __repr__(self) -> str:
        ctx = DumpContext()
        self._dump(ctx)
        return f"Int{self.width}({ctx.out.decode()})"

    def __lt__(self, other: Int[N], /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __le__(self, other: Int[N], /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __truediv__(self, other: Int[N], /) -> Int[N]:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __mod__(self, other: Int[N], /) -> Int[N]:  # pyright: ignore[reportIncompatibleMethodOverride]
        raise NotImplementedError

    def __rshift__(self, other: Uint[N], /) -> Int[N]:
        raise NotImplementedError

    # TODO: into()


class Placeholder[N: int](Uint[N]):
    __slots__ = ()


class Value[N: int](Placeholder[N]):
    __slots__ = ("_value",)
    __match_args__ = ("_value",)

    def __init__(self, value: int, /):
        assert 0 <= value < (1 << self.width)
        self._value = value

    def reveal(self) -> int | None:
        return self._value

    def _dump(self, ctx: DumpContext) -> None:
        if self.width % 8 == 0:
            ctx.write(b"#x" + self._value.to_bytes(self.width // 8).hex().encode())
        else:
            ctx.write(b"#b" + bin(self._value)[2:].zfill(self.width).encode())


class Symbol[N: int](Placeholder[N]):
    __slots__ = ("_name",)
    __match_args__ = ("_name",)

    def __init__(self, name: str, /):
        self._name = name.encode()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.add(
            self._name,
            (b"(declare-fun %s () (_ BitVec %d))" % (self._name, self.width)),
        )
        ctx.write(self._name)


class Not[N: int](Placeholder[N]):
    __slots__ = ("_term",)
    __match_args__ = ("_term",)

    def __init__(self, term: BitVector[N], /):
        self._term = term

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvnot ")
        self._term._dump(ctx)
        ctx.write(b")")


class Binary[N: int](Placeholder[N]):
    __slots__ = ("_left", "_right")
    __match_args__ = ("_left", "_right")

    def __init__(self, left: BitVector[N], right: BitVector[N], /):
        self._left = left
        self._right = right


class And[N: int](Binary[N]):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvand ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


class Or[N: int](Binary[N]):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(bvor ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


class Xor[N: int](Binary[N]):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(xor ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


def rewrite[N: int](term: BitVector[N]) -> BitVector[N]:
    N: Any = Literal[term.width]
    mask = (1 << term.width) - 1
    match term:
        case Not(Value(v)):
            return Value[N](mask ^ v)
        case Not(Not(inner)):  # ~(~X) => X
            return inner
        case And(Value(mask), x) | And(x, Value(mask)):  # X & 1111 => X
            return x
        case And(Value(0), x) | And(x, Value(0)):  # X & 0000 => 0000
            return Value[N](0)
        case And(x, y) if x == y:  # X & X => X
            return x
        case And(x, Not(y)) | And(Not(y), x) if x == y:  # X & ~X => 0000
            return Value[N](0)
        case Or(Value(mask), x) | Or(x, Value(mask)):  # X | 1111 => 1111
            return Value[N](mask)
        case Or(Value(0), x) | Or(x, Value(0)):  # X | 0000 => X
            return x
        case Or(x, y) if x == y:  # X | X => X
            return x
        case Or(x, Not(y)) | Or(Not(y), x) if x == y:  # X | ~X => 1111
            return Value[N](mask)
        case Xor(Value(mask), x) | Xor(x, Value(mask)):  # X ^ 1111 => ~X
            return Not[N](x)
        case Xor(Value(0), x) | Xor(x, Value(0)):  # X ^ 0000 => X
            return x
        case Xor(x, y) if x == y:  # X ^ X => 0000
            return Value[N](0)
        case Xor(x, Not(y)) | Xor(Not(y), x) if x == y:  # X ^ ~X => 1111
            return Value[N](mask)
        case _:
            return term
