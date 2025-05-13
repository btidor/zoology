"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass
from functools import reduce
from itertools import chain
import math
from subprocess import Popen, PIPE
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

            raise TypeError(
                f"unsupported type parameter passed to {self.__name__}[...]"
            )

        name = self.__name__ + "[" + k.__name__ + ", " + v.__name__ + "]"
        if name not in self._ccache:
            cls = type(name, (self,), {"_key": k, "_value": v, "__slots__": ()})
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

    @abc.abstractmethod
    def __repr__(self) -> str: ...


type BooleanTerm = bool | str | NotOp | AndOp | OrOp | XorOp | BvCmpOp


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

    def dump(self, defs: set[str]) -> str:
        return f"(not {dump(self.arg, defs)})"


@dataclass(frozen=True, slots=True)
class AndOp:
    args: frozenset[BooleanTerm]

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
                    args.update(term.args)  # A & A => A
                case _:
                    args.add(term)
        match len(args):
            case 0:
                return True
            case 1:
                return args.pop()
            case _:
                return AndOp(frozenset(args))

    def dump(self, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = f"(and {s} {dump(args.pop(), defs)})"
        return s


@dataclass(frozen=True, slots=True)
class OrOp:
    args: frozenset[BooleanTerm]

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
                    args.update(term.args)  # A | A => A
                case _:
                    args.add(term)
        match len(args):
            case 0:
                return False
            case 1:
                return args.pop()
            case _:
                return OrOp(frozenset(args))

    def dump(self, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = f"(or {s} {dump(args.pop(), defs)})"
        return s


@dataclass(frozen=True, slots=True)
class XorOp:
    base: bool
    args: frozenset[BooleanTerm]

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
                    if term in deferred:  # A ^ A => False (nop)
                        deferred.remove(term)
                    else:
                        deferred.add(term)
                case _:
                    if term in args:  # A ^ A => False (nop)
                        args.remove(term)
                    else:
                        args.add(term)
        for d in deferred:
            if d.arg in args:  # A ^ ~A => True
                assert not isinstance(d.arg, XorOp)
                args.remove(d.arg)
                invert ^= True
            else:
                args.add(d)
        return XorOp(invert, frozenset(args)) if args else invert

    def dump(self, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = f"(xor {s} {dump(args.pop(), defs)})"
        if self.base is True:
            s = f"(xor {s} true)"
        return s


class Constraint(Symbolic):
    __slots__ = ()
    _term: BooleanTerm

    def __init__(self, value: bool | str, /):
        self._term = value  # pyright: ignore

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({dump(self._term, set(['_pretty']))})"

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
        assert then.width == else_.width
        return then._from_term(IteOp.apply(self._term, then._term, else_._term))  # pyright: ignore

    def reveal(self) -> bool | None:
        return self._term if isinstance(self._term, bool) else None


type BitvectorTerm = (
    int
    | str
    | BvNotOp
    | BvAndOp
    | BvOrOp
    | BvXorOp
    | BvArithOp
    | BvMulOp
    | BvDivOp
    | BvModOp
    | BvShiftOp
    | IteOp
    | ExtractOp
    | ExtendOp
    | ConcatOp
    | SelectOp
)


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
            case BvArithOp(base, args):  # ~(A + B) => ~A + ~B - 1
                inv = list[BitvectorTerm]()
                inv.append(BvNotOp.apply(width, base))
                for arg in args:
                    inv.append(BvNotOp.apply(width, arg))
                    inv.append(1)
                return BvArithOp.apply(width, *inv)
            case _:
                return BvNotOp(term)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"(bvnot {dump(self.arg, defs, width)})"


@dataclass(frozen=True, slots=True)
class BvAndOp:
    mask: int
    args: frozenset[BitvectorTerm]

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
                    args.update(term.args)  # A & A => A
                case BvNotOp():
                    deferred.add(term)
                case _:
                    args.add(term)
        for term in deferred:
            if term.arg in args:
                return 0  # A & ~A => 0
            else:
                args.add(term)
        if mask == (1 << width) - 1:  # 0xFF & A => 0xFF
            return mask
        return BvAndOp(mask, frozenset(args)) if args else mask

    def dump(self, width: int, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = f"(bvand {s} {dump(args.pop(), defs, width)})"
        if self.mask != (1 << width) - 1:
            s = f"(bvand {s} {dump(self.mask, defs, width)})"
        return s


@dataclass(frozen=True, slots=True)
class BvOrOp:
    mask: int
    args: frozenset[BitvectorTerm]

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
                    args.update(term.args)  # A | A => A
                case BvNotOp():
                    deferred.add(term)
                case _:
                    args.add(term)
        for term in deferred:
            if term.arg in args:
                return (1 << width) - 1  # A | ~A => 0xFF
            else:
                args.add(term)
        if mask == 0:  # 0 | A => 0
            return mask
        return BvOrOp(mask, frozenset(args)) if args else mask

    def dump(self, width: int, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = f"(bvor {s} {dump(args.pop(), defs, width)})"
        if self.mask != 0:
            s = f"(bvor {s} {dump(self.mask, defs, width)})"
        return s


@dataclass(frozen=True, slots=True)
class BvXorOp:
    base: int
    args: frozenset[BitvectorTerm]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        mask = (1 << width) - 1
        base = 0
        args = set[BitvectorTerm]()
        deferred = set[BvNotOp]()
        for term in terms:
            match term:
                case int():
                    base ^= term
                case BvXorOp():
                    base ^= term.base
                    for arg in term.args:
                        if arg in args:  # A ^ A => 0
                            args.remove(arg)
                        else:
                            args.add(arg)
                case BvNotOp():
                    deferred.add(term)
                case _:
                    args.add(term)
        for term in deferred:
            if term.arg in args:
                args.remove(term.arg)
                base ^= mask  # A ^ ~A => 0xFF
            else:
                args.add(term)
        return BvXorOp(mask, frozenset(args)) if args else base

    def dump(self, width: int, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(self.base, defs, width)
        while args:
            s = f"(bvxor {s} {dump(args.pop(), defs, width)})"
        return s


@dataclass(frozen=True, slots=True)
class BvArithOp:
    base: int
    args: tuple[BitvectorTerm, ...]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        base = 0
        limit = 1 << width
        queue = list(terms)
        args = list[BitvectorTerm]()
        deferred = list[BvNotOp]()
        while queue:
            match term := queue.pop():
                case int():
                    base = (base + term) % limit
                case BvArithOp():
                    base = (base + term.base) % limit
                    queue.extend(term.args)
                case BvNotOp():
                    deferred.append(term)
                case _:
                    args.append(term)
        for term in deferred:
            if term.arg in args:  # A + ~A => 0xFF
                args.remove(term.arg)
                base = (base + limit - 1) % limit
            else:
                args.append(term)
        return BvArithOp(base, tuple(args)) if args else base

    def dump(self, width: int, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = f"(bvadd {s} {dump(args.pop(), defs, width)})"
        if self.base:
            s = f"(bvadd {dump(self.base, defs, width)} {s})"
        return s


@dataclass(frozen=True, slots=True)
class BvMulOp:
    base: int
    args: tuple[BitvectorTerm, ...]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        base = 1
        limit = 1 << width
        args = list[BitvectorTerm]()
        for term in terms:
            match term:
                case int():
                    base = (base * term) % limit
                case BvMulOp():
                    args.extend(term.args)
                case _:
                    args.append(term)
        if base == 0:
            return 0
        elif not args:
            return base
        elif base & (base - 1) == 0:  # https://stackoverflow.com/a/57025941
            n = int(math.log(base, 2))
            args[0] = BvShiftOp.apply(width, args[0], n, "L")
            base = 1

        if base == 1 and len(args) == 1:
            return args[0]
        return BvMulOp(base, tuple(args))

    def dump(self, width: int, defs: set[str]) -> str:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = f"(bvmul {s} {dump(args.pop(), defs, width)})"
        if self.base:
            s = f"(bvmul {dump(self.base, defs, width)} {s})"
        return s


@dataclass(frozen=True, slots=True)
class BvDivOp:
    left: BitvectorTerm
    right: BitvectorTerm
    signed: bool

    @classmethod
    def apply(
        cls, width: int, left: BitvectorTerm, right: BitvectorTerm, signed: bool
    ) -> BitvectorTerm:
        limit = 1 << width
        match (left, right, signed):
            case _, 0, _:
                return limit - 1
            case int(), int(), False:
                return left // right
            case int(), int(), True:
                return to_unsigned(
                    width, to_signed(width, left) // to_signed(width, right)
                )
            case _, int(), False if right & (right - 1) == 0:
                n = int(math.log(right, 2))
                return BvShiftOp.apply(width, left, n, "RS" if signed else "RU")
            case _:
                return BvDivOp(left, right, signed)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"(bv{'s' if self.signed else 'u'}div {dump(self.left, defs, width)} {dump(self.right, defs, width)})"


@dataclass(frozen=True, slots=True)
class BvModOp:
    left: BitvectorTerm
    right: BitvectorTerm
    signed: bool

    @classmethod
    def apply(
        cls, width: int, left: BitvectorTerm, right: BitvectorTerm, signed: bool
    ) -> BitvectorTerm:
        match (left, right, signed):
            case _, 0, _:
                return left
            case int(), int(), False:
                return left % right
            case int(), int(), True:
                return to_unsigned(
                    width, to_signed(width, left) % to_signed(width, right)
                )
            case _:
                return BvModOp(left, right, signed)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"(bv{'s' if self.signed else 'u'}rem {dump(self.left, defs, width)} {dump(self.right, defs, width)})"


@dataclass(frozen=True, slots=True)
class BvCmpOp:
    width: int
    left: BitvectorTerm
    right: BitvectorTerm
    kind: (
        Literal["EQ"]
        | Literal["ULT"]
        | Literal["ULE"]
        | Literal["SLT"]
        | Literal["SLE"]
    )

    @classmethod
    def apply(
        cls,
        width: int,
        left: BitvectorTerm,
        right: BitvectorTerm,
        kind: Literal["EQ"]
        | Literal["ULT"]
        | Literal["ULE"]
        | Literal["SLT"]
        | Literal["SLE"],
    ) -> BooleanTerm:
        match (left, right, kind):
            case int(), int(), "EQ":
                return left == right
            case int(), int(), "ULT":
                return left < right
            case int(), int(), "ULE":
                return left <= right
            case int(), int(), "SLT":
                return to_signed(width, left) < to_signed(width, right)
            case int(), int(), "SLE":
                return to_signed(width, left) <= to_signed(width, right)
            case _:
                return BvCmpOp(width, left, right, kind)

    def dump(self, defs: set[str]) -> str:
        if "_pretty" in defs:
            match self.kind:
                case "EQ":
                    short = "="
                case "ULT":
                    short = "u<"
                case "ULE":
                    short = "u<="
                case "SLT":
                    short = "s<"
                case "SLE":
                    short = "s<="
            return f"({dump(self.left, defs, self.width)} {short} {dump(self.right, defs, self.width)})"
        else:
            match self.kind:
                case "EQ":
                    short = "="
                case "ULT":
                    short = "bvult"
                case "ULE":
                    short = "bvule"
                case "SLT":
                    short = "bvslt"
                case "SLE":
                    short = "bvsle"
            return f"({short} {dump(self.left, defs, self.width)} {dump(self.right, defs, self.width)})"


@dataclass(frozen=True, slots=True)
class BvShiftOp:
    term: BitvectorTerm
    shift: BitvectorTerm
    way: Literal["L"] | Literal["RU"] | Literal["RS"]

    @classmethod
    def apply(
        cls,
        width: int,
        term: BitvectorTerm,
        shift: BitvectorTerm,
        way: Literal["L"] | Literal["RU"] | Literal["RS"],
    ) -> BitvectorTerm:
        limit = 1 << width
        match (term, shift, way):
            case _, 0, _:
                return term
            case int(), int(), "L":
                return (term << shift) % limit
            case int(), int(), "RU":
                return (term >> shift) % limit
            case int(), int(), "RS":
                return to_unsigned(width, (to_signed(width, term) >> shift) % limit)
            case _, int(), "L" | "RU" if shift >= width:
                return 0
            case _:
                return BvShiftOp(term, shift, way)

    def dump(self, width: int, defs: set[str]) -> str:
        match self.way:
            case "L":
                short = "bvshl"
            case "RU":
                short = "bvlshr"
            case "RS":
                short = "bvashr"
        return (
            f"({short} {dump(self.term, defs, width)} {dump(self.shift, defs, width)})"
        )


@dataclass(frozen=True, slots=True)
class IteOp:
    cond: BooleanTerm
    left: BitvectorTerm
    right: BitvectorTerm

    @classmethod
    def apply(
        cls,
        cond: BooleanTerm,
        left: BitvectorTerm,
        right: BitvectorTerm,
    ) -> BitvectorTerm:
        match (cond, left, right):
            case True, _, _:
                return left
            case False, _, _:
                return right
            case _ if left == right:
                return left
            case _:
                return IteOp(cond, left, right)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"(ite {dump(self.cond, defs)} {dump(self.left, defs, width)} {dump(self.right, defs, width)})"


@dataclass(frozen=True, slots=True)
class ExtractOp:
    term: BitvectorTerm
    prior: int

    @classmethod
    def apply(cls, term: BitvectorTerm, rightmost: int, prior: int) -> BitvectorTerm:
        assert rightmost > 0
        match (term, rightmost):
            case int(), _:
                return term & ((1 << rightmost) - 1)
            case _:
                return ExtractOp(term, prior)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"((_ extract {width - 1} 0) {dump(self.term, defs, self.prior)})"


@dataclass(frozen=True, slots=True)
class ExtendOp:
    term: BitvectorTerm
    extra: int
    signed: bool

    @classmethod
    def apply(
        cls, width: int, term: BitvectorTerm, extra: int, signed: bool
    ) -> BitvectorTerm:
        assert extra > 0
        match (term, extra, signed):
            case int(), _, False:
                return term
            case int(), _, True:
                return to_unsigned(width + extra, to_signed(width, term))
            case _:
                return ExtendOp(term, extra, signed)

    def dump(self, width: int, defs: set[str]) -> str:
        if "_pretty" in defs:
            return f"(...{dump(self.term, defs, width - self.extra)})"
        else:
            return f"(concat {dump(0, defs, self.extra)} {dump(self.term, defs, width - self.extra)})"


@dataclass(frozen=True, slots=True)
class ConcatOp:
    width: int
    terms: tuple[BitvectorTerm, ...]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        i = 0
        for t in terms:
            if not isinstance(t, int):
                break
            i = (i << width) | t
        else:
            return i
        return ConcatOp(width, terms)

    def dump(self, width: int, defs: set[str]) -> str:
        return f"(concat {' '.join(dump(t, defs, self.width) for t in self.terms)})"


class BitVector[N: int](
    Symbolic, metaclass=abc.ABCMeta if TYPE_CHECKING else BitVectorMeta
):
    __slots__ = ()
    width: Final[int]  # pyright: ignore
    _term: BitvectorTerm

    def __init__(self, value: int | str, /) -> None:
        self._term = value  # pyright: ignore

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({dump(self._term, set(['_pretty']), self.width)})"

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
        return self._from_term(BvXorOp.apply(self.width, self._term, other._term))

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
        assert self.width == other.width
        return self._from_term(BvMulOp.apply(self.width, self._term, other._term))

    @abc.abstractmethod
    def __truediv__(self, other: Self, /) -> Self: ...

    @abc.abstractmethod
    def __mod__(self, other: Self, /) -> Self: ...

    def __lshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvShiftOp.apply(self.width, self._term, other._term, "L")
        )

    @abc.abstractmethod
    def __rshift__(self, other: Uint[N], /) -> Self: ...

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            BvCmpOp.apply(self.width, self._term, other._term, "EQ")
        )

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            NotOp.apply(BvCmpOp.apply(self.width, self._term, other._term, "EQ"))
        )

    def __hash__(self) -> int:
        return self._term.__hash__()


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            BvCmpOp.apply(self.width, self._term, other._term, "ULT")
        )

    def __le__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            BvCmpOp.apply(self.width, self._term, other._term, "ULE")
        )

    def __truediv__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvDivOp.apply(self.width, self._term, other._term, False)
        )

    def __mod__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvModOp.apply(self.width, self._term, other._term, False)
        )

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvShiftOp.apply(self.width, self._term, other._term, "RU")
        )

    @overload
    def into[M: int](self: Uint[N], other: type[Int[N]], /) -> Int[N]: ...

    @overload
    def into[M: int](self: Uint[N], other: type[Uint[M]], /) -> Uint[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        if self.width == other.width:
            return other._from_term(self._term)
        elif self.width < other.width:
            return other._from_term(
                ExtendOp.apply(self.width, self._term, other.width - self.width, False)
            )
        else:
            return other._from_term(
                ExtractOp.apply(self._term, other.width, self.width)
            )

    def reveal(self) -> int | None:
        return self._term if isinstance(self._term, int) else None


class Int[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            BvCmpOp.apply(self.width, self._term, other._term, "SLT")
        )

    def __le__(self, other: Self, /) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            BvCmpOp.apply(self.width, self._term, other._term, "SLE")
        )

    def __truediv__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(BvDivOp.apply(self.width, self._term, other._term, True))

    def __mod__(self, other: Self, /) -> Self:
        assert self.width == other.width
        return self._from_term(BvModOp.apply(self.width, self._term, other._term, True))

    def __rshift__(self, other: Uint[N], /) -> Self:
        assert self.width == other.width
        return self._from_term(
            BvShiftOp.apply(self.width, self._term, other._term, "RS")
        )

    @overload
    def into[M: int](self: Int[N], other: type[Uint[N]], /) -> Uint[N]: ...

    @overload
    def into[M: int](self: Int[N], other: type[Int[M]], /) -> Int[M]: ...

    def into[M: int](self, other: type[BitVector[M]], /) -> BitVector[M]:
        if self.width == other.width:
            return other._from_term(self._term)
        elif self.width < other.width:
            return other._from_term(
                ExtendOp.apply(self.width, self._term, other.width - self.width, True)
            )
        else:
            return other._from_term(
                ExtractOp.apply(self._term, other.width, self.width)
            )

    def reveal(self) -> int | None:
        return (
            to_signed(self.width, self._term) if isinstance(self._term, int) else None
        )


@dataclass(frozen=True, slots=True)
class UninterpretedTerm:
    name: str
    width: tuple[int, int]

    def dump(self, width: tuple[int, int], defs: set[str]) -> str:
        defs.add(
            f"(declare-fun {self.name} () (Array (_ BitVec {width[0]}) (_ BitVec {width[1]})))"
        )
        return self.name


@dataclass(frozen=True, slots=True)
class ArrayTerm:
    default: BitvectorTerm | UninterpretedTerm
    width: tuple[int, int]
    base: frozenset[tuple[int, BitvectorTerm]] = frozenset()
    writes: tuple[tuple[BitvectorTerm, BitvectorTerm], ...] = ()

    @classmethod
    def apply(
        cls, array: ArrayTerm, key: BitvectorTerm, value: BitvectorTerm
    ) -> ArrayTerm:
        base = dict(array.base)
        writes = list(array.writes)
        if array.writes or not isinstance(key, int):
            writes.append((key, value))
        else:
            base[key] = value
        return ArrayTerm(
            array.default, array.width, frozenset(base.items()), tuple(writes)
        )

    def dump(self, width: tuple[int, int], defs: set[str]) -> str:
        if "_pretty" in defs:
            if isinstance(self.default, UninterpretedTerm):
                stores = [("default", self.default.name)]
            else:
                stores = [("default", dump(self.default, defs, width[1]))]
            for k, v in chain(self.base, self.writes):
                stores.append((dump(k, defs, width[0]), dump(k, defs, width[1])))
            return str(dict(stores))
        else:
            if isinstance(self.default, UninterpretedTerm):
                s = dump(self.default, defs, width)
            else:
                s = f"((as const (Array (_ BitVec {width[0]}) (_ BitVec {width[1]}))) {dump(self.default, defs, width[1])})"
            for k, v in chain(self.base, self.writes):
                s = f"(store {s} {dump(k, defs, width[0])} {dump(v, defs, width[1])})"
            return s


@dataclass(frozen=True, slots=True)
class SelectOp:
    array: ArrayTerm | UninterpretedTerm
    key: BitvectorTerm

    @classmethod
    def apply(cls, array: ArrayTerm, key: BitvectorTerm) -> BitvectorTerm:
        if array.writes and key == array.writes[-1][0]:
            return array.writes[-1][1]
        elif array.writes or not isinstance(key, int):
            return SelectOp(array, key)
        elif key in (tmp := dict(array.base)):
            return tmp[key]
        elif isinstance(array.default, UninterpretedTerm):
            return SelectOp(array.default, key)
        else:
            return array.default

    def dump(self, width: int, defs: set[str]) -> str:
        if "_pretty" in defs:
            return f"({dump(self.array, defs, self.array.width)}[{dump(self.key, defs, self.array.width[0])}])"
        else:
            return f"(select {dump(self.array, defs, self.array.width)} {dump(self.key, defs, self.array.width[0])})"


class Array[K: Uint[Any] | Int[Any], V: Uint[Any] | Int[Any]](
    metaclass=type if TYPE_CHECKING else ArrayMeta
):
    __slots__ = ("_array",)
    __hash__: ClassVar[None] = None  # pyright: ignore[reportIncompatibleMethodOverride]

    def __init__(self, value: V | str, /) -> None:
        width: tuple[int, int] = (self._key.width, self._value.width)  # pyright: ignore
        match value:
            case str():
                self._array = ArrayTerm(UninterpretedTerm(value, width), width)  # pyright: ignore[reportPrivateUsage]
            case BitVector():
                self._array = ArrayTerm(value._term, width)  # pyright: ignore[reportPrivateUsage]

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({dump(self._array, set(['_pretty']), self._array.width)})"

    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise TypeError("arrays cannot be compared for equality.")

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Never, /
    ) -> Never:
        raise TypeError("arrays cannot be compared for equality.")

    def __getitem__(self, key: K) -> V:
        return self._value(SelectOp.apply(self._array, key._term))  # pyright: ignore

    def __setitem__(self, key: K, value: V) -> None:
        self._array = ArrayTerm.apply(self._array, key._term, value._term)  # pyright: ignore[reportPrivateUsage]


class Solver:
    def __init__(self) -> None:
        self.constraint = Constraint(True)
        self.model = None

    def add(self, assertion: Constraint, /) -> None:
        self.constraint &= assertion
        self.model = None

    def check(self, *assumptions: Constraint) -> bool:
        defs = set[str]()
        constraint = reduce(Constraint.__and__, assumptions, self.constraint)
        match constraint._term:  # pyright: ignore[reportPrivateUsage]
            case bool() as b:
                self.model = {}
                return b
            case str() as s:
                self.model = {s: True}
                return True
            case term:
                sexpr = term.dump(defs)
        smt = "\n".join([*defs, f"(assert {sexpr})", "(check-sat)"])
        p = Popen(["z3", "/dev/stdin"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        out, err = p.communicate(smt.encode())
        match out.decode().strip():
            case "sat":
                return True
            case "unsat":
                return False
            case _:
                raise RuntimeError(out, err)

    @overload
    def evaluate(self, s: Constraint, /) -> bool: ...

    @overload
    def evaluate[N: int](self, s: Uint[N] | Int[N], /) -> int: ...

    @overload
    def evaluate[N: int, M: int](
        self, s: Array[Uint[N], Uint[M]], /
    ) -> dict[int, int]: ...

    def evaluate[N: int, M: int](
        self, sym: Constraint | Uint[N] | Int[N] | Array[Uint[N], Uint[M]], /
    ) -> bool | int | dict[int, int]:
        if isinstance(sym, Array):
            raise NotImplementedError
        match sym._term:  # pyright: ignore[reportPrivateUsage]
            case bool() as b:
                return b
            case int() as i:
                return i
            case str() as s:
                raise NotImplementedError(s)
            case other:
                raise NotImplementedError(other)


@overload
def dump(term: BooleanTerm, defs: set[str], width: None = None) -> str: ...


@overload
def dump(term: BitvectorTerm, defs: set[str], width: int) -> str: ...


@overload
def dump(
    term: ArrayTerm | UninterpretedTerm, defs: set[str], width: tuple[int, int]
) -> str: ...


def dump(
    term: BooleanTerm | BitvectorTerm | ArrayTerm | UninterpretedTerm,
    defs: set[str],
    width: None | int | tuple[int, int] = None,
) -> str:
    match term:
        case True:
            return "true"
        case False:
            return "false"
        case int():
            assert isinstance(width, int)
            if "_pretty" in defs:
                return hex(to_signed(width, term))
            elif width % 8 == 0:
                return "#x" + term.to_bytes(width // 8).hex()
            else:
                return "#b" + bin(term)[2:].zfill(width)
        case str():
            if width is None:
                defs.add(f"(declare-fun {term} () Bool)")
            else:
                defs.add(f"(declare-fun {term} () (_ BitVec {width}))")
            return term
        case _:
            return term.dump(defs) if width is None else term.dump(width, defs)  # pyright: ignore


Uint8 = Uint[Literal[8]]
Uint64 = Uint[Literal[64]]
Uint128 = Uint[Literal[128]]
Uint160 = Uint[Literal[160]]
Uint256 = Uint[Literal[256]]
Uint257 = Uint[Literal[257]]
Uint512 = Uint[Literal[512]]

Int256 = Int[Literal[256]]
Int257 = Int[Literal[257]]


class NarrowingError(Exception):
    pass


class ConstrainingError(Exception):
    pass


def describe[N: int](s: Uint[N]) -> str:
    raise NotImplementedError


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return (a.into(Uint257) + b.into(Uint257)).into(Int257) >= Int257(0)


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return a >= b


def compact_array[N: int, M: int](
    solver: Solver, constraint: Constraint, a: Array[Uint[N], Uint[M]]
) -> Constraint:
    raise NotImplementedError


def compact_helper[N: int](
    solver: Solver, constraint: Constraint, a: Uint[N], b: Uint[N]
) -> tuple[Constraint, Uint[N]]:
    raise NotImplementedError


def concat_bytes(*bytes: Uint8) -> Uint[Any]:
    cls = Uint[Literal[8 * len(bytes)]]  # pyright: ignore
    return cls._from_term(ConcatOp.apply(8, *(b._term for b in bytes)))  # pyright: ignore


def concat_words(*words: Uint256) -> Uint[Any]:
    cls = Uint[Literal[256 * len(words)]]  # pyright: ignore
    return cls._from_term(ConcatOp.apply(256, *(w._term for w in words)))  # pyright: ignore


def explode_bytes(v: Uint256) -> list[Uint8]:
    r = list[Uint8]()
    for _ in range(32):
        r.append(v.into(Uint8))
        v >>= Uint256(8)
    return r


def iff(a: Constraint, b: Constraint) -> Constraint:
    raise NotImplementedError


def implies(a: Constraint, b: Constraint) -> Constraint:
    raise NotImplementedError


def prequal[N: int](a: Uint[N], b: Uint[N]) -> bool:
    raise NotImplementedError


def get_constants[N: int](v: Constraint | Uint[N] | Int[N]) -> Any:
    raise NotImplementedError


def substitute(s: Symbolic, b: Any) -> Any:
    raise NotImplementedError


def substitute2[N: int](s: Uint[N], b: Any) -> Uint[N]:
    raise NotImplementedError


def to_signed(width: int, value: int) -> int:
    if value & (1 << (width - 1)):
        return -((((1 << width) - 1) ^ value) + 1)
    return value


def to_unsigned(width: int, value: int) -> int:
    if value < 0:
        return (((1 << width) - 1) ^ -value) + 1
    return value
