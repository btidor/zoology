"""TODO."""
# ruff: noqa

from __future__ import annotations

import abc
from typing import TYPE_CHECKING, Any, Never
from ._base import DumpContext, Symbolic


class Meta(abc.ABCMeta):
    def __call__(cls, *args: Any) -> Constraint:
        if cls == Constraint:  # pyright: ignore
            match args:
                case (bool() as b,):
                    return Value(b)
                case (str() as s,):
                    return Symbol(s)
                case _:
                    raise TypeError(f"cannot init Constraint with args: {args}")
        else:
            return super().__call__(*args)


# This prevents the metaclass from breaking __init__() type checking:
TMeta = abc.ABCMeta if TYPE_CHECKING else Meta


class Constraint(Symbolic, metaclass=TMeta):
    __slots__ = ()

    def __init__(self, value: bool | str, /):
        raise TypeError("__init__ should be handled by metaclass")

    def __repr__(self) -> str:
        ctx = DumpContext()
        self._dump(ctx)
        return f"Constraint({ctx.out.decode()})"

    def __invert__(self) -> Constraint:
        return rewrite_constraint(Not(self))

    def __and__(self, other: Constraint, /) -> Constraint:
        return rewrite_constraint(And(self, other))

    def __or__(self, other: Constraint, /) -> Constraint:
        return rewrite_constraint(Or(self, other))

    def __xor__(self, other: Constraint, /) -> Constraint:
        return rewrite_constraint(Xor(self, other))

    def __bool__(self) -> Never:
        raise TypeError("cannot use Constraint in a boolean context")

    # TODO: ite()

    def reveal(self) -> bool | None:
        return None


class Value(Constraint):
    __slots__ = ("_value",)
    __match_args__ = ("_value",)

    def __init__(self, value: bool, /):
        self._value = value

    def reveal(self) -> bool | None:
        return self._value

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self._value else b"false")


class Symbol(Constraint):
    __slots__ = ("_name",)
    __match_args__ = ("_name",)

    def __init__(self, name: str, /):
        self._name = name.encode()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.add(self._name, (b"(declare-fun %s () Bool)" % self._name))
        ctx.write(self._name)


class Not(Constraint):
    __slots__ = ("_term",)
    __match_args__ = ("_term",)

    def __init__(self, term: Constraint, /):
        self._term = term

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(not ")
        self._term._dump(ctx)
        ctx.write(b")")


class Binary(Constraint):
    __slots__ = ("_left", "_right")
    __match_args__ = ("_left", "_right")

    def __init__(self, left: Constraint, right: Constraint, /):
        self._left = left
        self._right = right


class And(Binary):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(and ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


class Or(Binary):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(or ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


class Xor(Binary):
    __slots__ = ()

    def _dump(self, ctx: DumpContext) -> None:
        ctx.write(b"(xor ")
        self._left._dump(ctx)
        ctx.write(b" ")
        self._right._dump(ctx)
        ctx.write(b")")


def rewrite_constraint(term: Constraint) -> Constraint:
    match term:
        case Not(Not(term)):
            return term
        case _:
            return term
