"""TODO."""
# ruff: noqa

from __future__ import annotations
import abc

from ._base import Symbolic
from ._constraint import Constraint


class BitVector[N: int](Symbolic):
    __slots__ = ()
    width: Final[int]  # pyright: ignore

    def __init__(self, value: int | str, /) -> None:
        self._term = value  # pyright: ignore

    def __repr__(self) -> str:
        raise NotImplementedError

    @abc.abstractmethod
    def __lt__(self, other: BitVector[N], /) -> Constraint: ...

    @abc.abstractmethod
    def __le__(self, other: BitVector[N], /) -> Constraint: ...

    def __invert__(self) -> BitVector[N]:
        raise NotImplementedError

    def __and__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

    def __or__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

    def __xor__(self, other: BitVector[N], /) -> BitVector[N]:
        raise NotImplementedError

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

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: BitVector[N], /
    ) -> Constraint:
        raise NotImplementedError

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: BitVector[N], /
    ) -> Constraint:
        raise NotImplementedError


class Uint[N: int](BitVector[N]):
    __slots__ = ()

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

    @abc.abstractmethod
    def reveal(self) -> int | None: ...


class Int[N: int](BitVector[N]):
    __slots__ = ()

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

    @abc.abstractmethod
    def reveal(self) -> int | None: ...
