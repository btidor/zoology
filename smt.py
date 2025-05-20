"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

import abc
from collections import defaultdict
import copy
from dataclasses import dataclass
from functools import reduce
from itertools import chain
import math
from subprocess import Popen, PIPE
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    ClassVar,
    Final,
    Generator,
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

type Model = dict[str, bool | int | dict[int, int]]

type Term = BooleanTerm | BitvectorTerm | ArrayTerm | UninterpretedTerm


def hashcache[T: Any](cls: type[T]) -> type[T]:
    cls.__slots__ = (*cls.__slots__, "_hash")
    cls._hash = cls.__hash__(cls)
    h: Callable[[T], int] = lambda c: c._hash
    cls.__hash__ = h
    return cls


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


type BooleanTerm = bool | str | NotOp | AndOp | OrOp | XorOp | CmpOp


@hashcache
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

    def dump(self, defs: set[str]) -> tuple[str, ...]:
        return ("(not", *dump(self.arg, defs), ")")

    def eval(self, model: Model) -> bool:
        return not eval(self.arg, model)

    def walk(self) -> Generator[Term]:
        yield from walk(self.arg)

    def substitute(self, subs: dict[str, Term]) -> BooleanTerm:
        return NotOp.apply(_substitute(self.arg, subs))


@hashcache
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

    def dump(self, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = ("(and", *s, *dump(args.pop(), defs), ")")
        return s

    def eval(self, model: Model) -> bool:
        return reduce(lambda p, q: p and eval(q, model), self.args, True)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, subs: dict[str, Term]) -> BooleanTerm:
        return AndOp.apply(*(_substitute(a, subs) for a in self.args))


@hashcache
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

    def dump(self, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = ("(or", *s, *dump(args.pop(), defs), ")")
        return s

    def eval(self, model: Model) -> bool:
        return reduce(lambda p, q: p or eval(q, model), self.args, False)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, subs: dict[str, Term]) -> BooleanTerm:
        return OrOp.apply(*(_substitute(a, subs) for a in self.args))


@hashcache
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

    def dump(self, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs)
        while args:
            s = ("(xor", *s, *dump(args.pop(), defs), ")")
        if self.base is True:
            s = ("(xor", *s, "true)")
        return s

    def eval(self, model: Model) -> bool:
        return reduce(lambda p, q: p ^ eval(q, model), self.args, False)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, subs: dict[str, Term]) -> BooleanTerm:
        return XorOp.apply(self.base, *(_substitute(a, subs) for a in self.args))


class Constraint(Symbolic):
    __slots__ = ()
    _term: BooleanTerm

    def __init__(self, value: bool | str, /):
        self._term = value  # pyright: ignore

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({prettify(self._term)})"

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
        return then._from_term(
            IteOp.apply(self._term, then._term, else_._term, then.width)  # pyright: ignore
        )

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


@hashcache
@dataclass(frozen=True, slots=True)
class BvNotOp:
    arg: BitvectorTerm
    minmax: tuple[int, int]

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
            case ConcatOp(w, terms):
                return ConcatOp.apply(w, *(BvNotOp.apply(w, t) for t in terms))
            case _:
                m, n = minmax(term, width)
                p, q = (mask - n, mask - m)
                assert 0 <= p <= q <= mask
                return BvNotOp(term, (p, q))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        return ("(bvnot", *dump(self.arg, defs, width), ")")

    def eval(self, width: int, model: Model) -> int:
        mask = (1 << width) - 1
        return mask ^ eval(self.arg, model, width)

    def walk(self) -> Generator[Term]:
        yield from walk(self.arg)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvNotOp.apply(width, _substitute(self.arg, subs, width))


@hashcache
@dataclass(frozen=True, slots=True)
class BvAndOp:
    mask: int
    args: frozenset[BitvectorTerm]
    minmax: tuple[int, int]

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
        if not args:
            return mask
        elif mask == 0:  # 0 & A => 0
            return mask
        elif len(args) == 1 and mask == (1 << width) - 1:  # 0xFF & A => A
            return args.pop()
        elif len(args) == 1 and isinstance(c := list(args)[0], ConcatOp):
            pushed = list[BitvectorTerm]()
            for term in reversed(c.terms):
                pushed.append(BvAndOp.apply(c.width, term, mask & ((1 << c.width) - 1)))
                mask >>= c.width
            return ConcatOp.apply(c.width, *reversed(pushed))
        else:
            n = reduce(
                lambda p, q: min(p, minmax(q, width)[1]), args, mask
            )  # 0 <= A & B <= min(A, B)
            assert 0 <= n <= mask
            return BvAndOp(mask, frozenset(args), (0, n)) if args else mask

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = ("(bvand", *s, *dump(args.pop(), defs, width), ")")
        if self.mask != (1 << width) - 1:
            s = ("(bvand", *s, *dump(self.mask, defs, width), ")")
        return s

    def eval(self, width: int, model: Model) -> int:
        mask = (1 << width) - 1
        return reduce(lambda p, q: p & eval(q, model, width), self.args, mask)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvAndOp.apply(
            width, self.mask, *(_substitute(a, subs, width) for a in self.args)
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvOrOp:
    mask: int
    args: frozenset[BitvectorTerm]
    minmax: tuple[int, int]

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
        if not args:
            return mask
        elif mask == (1 << width) - 1:  # 0xFF | A => 0xFF
            return mask
        elif len(args) == 1 and mask == 0:  # 0 | A => A
            return args.pop()
        elif len(args) == 1 and isinstance(c := list(args)[0], ConcatOp):
            pushed = list[BitvectorTerm]()
            for term in reversed(c.terms):
                pushed.append(BvOrOp.apply(c.width, term, mask & ((1 << c.width) - 1)))
                mask >>= c.width
            return ConcatOp.apply(c.width, *reversed(pushed))
        else:
            m = reduce(
                lambda p, q: max(p, minmax(q, width)[0]), args, mask
            )  # max(A, B) <= A | B <= limit
            assert 0 <= m < (1 << width)
            return (
                BvOrOp(mask, frozenset(args), (m, (1 << width) - 1)) if args else mask
            )

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = ("(bvor", *s, *dump(args.pop(), defs, width), ")")
        if self.mask != 0:
            s = ("(bvor", *s, *dump(self.mask, defs, width), ")")
        return s

    def eval(self, width: int, model: Model) -> int:
        return reduce(lambda p, q: p | eval(q, model, width), self.args, 0)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvOrOp.apply(
            width, self.mask, *(_substitute(a, subs, width) for a in self.args)
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvXorOp:
    base: int
    args: frozenset[BitvectorTerm]
    minmax: tuple[int, int]

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
        return BvXorOp(mask, frozenset(args), (0, (1 << width) - 1)) if args else base

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(self.base, defs, width)
        while args:
            s = ("(bvxor", *s, *dump(args.pop(), defs, width), ")")
        return s

    def eval(self, width: int, model: Model) -> int:
        return reduce(lambda p, q: p ^ eval(q, model, width), self.args, 0)

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvXorOp.apply(
            width, self.base, *(_substitute(a, subs, width) for a in self.args)
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvArithOp:
    base: int
    args: tuple[BitvectorTerm, ...]
    minmax: tuple[int, int]

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
        m, n = base, base
        safe = limit >> len(args)
        if base > 0:
            safe >>= 1
        good = False
        if base < safe:
            good = True
            for arg in args:
                p, q = minmax(arg, width)
                if q >= safe:
                    good = False
                    break
                m = min(m + p, limit - 1)
                n = min(n + q, limit - 1)
        if not good:
            unbase = to_signed(width, base)
            ungood = False
            unlimit = to_signed(width, (1 << (width - 1)))
            if unbase <= 0:
                ungood = True
                m, n = unbase, unbase
                for arg in args:
                    p, q = mm_to_signed(width, *minmax(arg, width))
                    if p < -safe or q > 0:
                        ungood = False
                        break
                    m = max(m + p, unlimit)
                    n = max(n + q, unlimit)
            if ungood:
                assert m <= 0 and n <= 0
                m, n = mm_to_unsigned(width, m, n)
            else:
                m, n = 0, limit - 1
        assert 0 <= m <= n < limit
        return BvArithOp(base, tuple(args), (m, n)) if args else base

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = ("(bvadd", *s, *dump(args.pop(), defs, width), ")")
        if self.base:
            s = ("(bvadd", *dump(self.base, defs, width), *s, ")")
        return s

    def eval(self, width: int, model: Model) -> int:
        limit = 1 << width
        return reduce(
            lambda p, q: (p + eval(q, model, width)) % limit, self.args, self.base
        )

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvArithOp.apply(
            width, self.base, *(_substitute(a, subs, width) for a in self.args)
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvMulOp:
    base: int
    args: tuple[BitvectorTerm, ...]
    minmax: tuple[int, int]

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
        if len(args) == 1:
            m, n = minmax(args[0], width)
            m = max(m * base, limit - 1)
            n = max(n * base, limit - 1)
        else:
            m, n = (0, limit - 1)
        return BvMulOp(base, tuple(args), (m, n))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        args = set(self.args)
        s = dump(args.pop(), defs, width)
        while args:
            s = ("(bvmul", *s, *dump(args.pop(), defs, width), ")")
        if self.base:
            s = ("(bvmul", *dump(self.base, defs, width), *s, ")")
        return s

    def eval(self, width: int, model: Model) -> int:
        limit = 1 << width
        return reduce(
            lambda p, q: (p * eval(q, model, width)) % limit, self.args, self.base
        )

    def walk(self) -> Generator[Term]:
        yield from walk(*self.args)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvMulOp.apply(
            width, self.base, *(_substitute(a, subs, width) for a in self.args)
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvDivOp:
    left: BitvectorTerm
    right: BitvectorTerm
    signed: bool
    minmax: tuple[int, int]

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
                if signed:
                    m, n = (0, limit)
                else:
                    m = 0
                    _, n = minmax(left, width)
                    if isinstance(right, int):
                        n //= right
                return BvDivOp(left, right, signed, (m, n))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        return (
            f"(bv{'s' if self.signed else 'u'}div",
            *dump(self.left, defs, width),
            *dump(self.right, defs, width),
            ")",
        )

    def eval(self, width: int, model: Model) -> int:
        if self.signed:
            return to_unsigned(
                width,
                to_signed(width, eval(self.left, model, width))
                // to_signed(width, eval(self.right, model, width)),
            )
        else:
            return eval(self.left, model, width) // eval(self.right, model, width)

    def walk(self) -> Generator[Term]:
        yield from walk(self.left, self.right)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvDivOp.apply(
            width,
            _substitute(self.left, subs, width),
            _substitute(self.right, subs, width),
            self.signed,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvModOp:
    left: BitvectorTerm
    right: BitvectorTerm
    signed: bool
    minmax: tuple[int, int]

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
                _, n = minmax(right, width)
                n -= 1
                if signed:
                    n = to_signed(width, n)
                return BvModOp(left, right, signed, (0, n))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        return (
            f"(bv{'s' if self.signed else 'u'}rem",
            *dump(self.left, defs, width),
            *dump(self.right, defs, width),
            ")",
        )

    def eval(self, width: int, model: Model) -> int:
        if self.signed:
            return to_unsigned(
                width,
                to_signed(width, eval(self.left, model, width))
                % to_signed(width, eval(self.right, model, width)),
            )
        else:
            return eval(self.left, model, width) % eval(self.right, model, width)

    def walk(self) -> Generator[Term]:
        yield from walk(self.left, self.right)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvModOp.apply(
            width,
            _substitute(self.left, subs, width),
            _substitute(self.right, subs, width),
            self.signed,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class CmpOp:
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
        r = cls._apply(width, left, right, kind)
        # if isinstance(r, bool):
        #     s = Solver()
        #     t = Constraint._from_term(CmpOp(width, left, right, kind))  # pyright: ignore[reportPrivateUsage]
        #     s.add(~t if r else t)
        #     assert not s.check(), f"MISMATCH-{r}: {kind} {left} {right}"
        return r

    @classmethod
    def _apply(
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
        if kind == "EQ" and isinstance(right, int):
            # normalize ints on lefthand side
            left, right = right, left
        match (left, right, kind):
            case int(), int(), "EQ":
                return left == right
            case _, _, "EQ" if left == right:
                return True
            case ConcatOp(w, t0), ConcatOp(w1, t1), "EQ" if w == w1 and len(t0) == len(
                t1
            ):
                return AndOp.apply(
                    *(CmpOp.apply(w, a, b, "EQ") for a, b in zip(t0, t1, strict=True))
                )
            case int(), int(), "ULT":
                return left < right
            case int(), int(), "ULE":
                return left <= right
            case int(), int(), "SLT":
                return to_signed(width, left) < to_signed(width, right)
            case int(), int(), "SLE":
                return to_signed(width, left) <= to_signed(width, right)
            case _, 0, "ULT":  # X < 0 => False
                return False
            case 0, x, "ULT":  # X > 0 => X != 0
                return NotOp.apply(CmpOp.apply(width, x, 0, "EQ"))
            case x, 0, "ULE":  # X <= 0 => X = 0
                return CmpOp.apply(width, x, 0, "EQ")
            case 0, _, "ULE":  # X >= 0 => True
                return True
            case IteOp(i, t, e), o, _:
                a = CmpOp.apply(width, t, o, kind)
                b = CmpOp.apply(width, e, o, kind)
                return OrOp.apply(AndOp.apply(i, a), AndOp.apply(NotOp.apply(i), b))
            case o, IteOp(i, t, e), _:
                a = CmpOp.apply(width, o, t, kind)
                b = CmpOp.apply(width, o, e, kind)
                return OrOp.apply(AndOp.apply(i, a), AndOp.apply(NotOp.apply(i), b))
            case int() as i, ExtendOp(t, x, False), "EQ":
                if i < (1 << (width - x)):
                    return CmpOp.apply(width - x, t, i, "EQ")
                else:
                    return False
            case int() as i, ConcatOp(w, terms), "EQ":
                assert width % w == 0
                ints = list[int]()
                mask = (1 << w) - 1
                for _ in terms:
                    ints.append(i & mask)
                    i >>= w
                ints.reverse()
                return AndOp.apply(
                    *(CmpOp.apply(w, j, t, "EQ") for j, t in zip(ints, terms))
                )
            case int() as i, BvArithOp(base, args), "EQ" if base != 0:
                limit = 1 << width
                delta = i - base
                if delta < 0:
                    delta += limit
                assert 0 <= delta < limit
                return CmpOp.apply(width, delta, BvArithOp.apply(width, *args), "EQ")
            case int() as i, BvNotOp(arg), "EQ":
                mask = (1 << width) - 1
                return CmpOp.apply(width, i ^ mask, arg, "EQ")
            case _:
                pass
        p, q = minmax(left, width)
        r, s = minmax(right, width)
        match kind:
            case "EQ" if q < r or s < p:
                return False
            case "ULT" if q < r:
                return True
            case "ULE" if q <= r:
                return True
            case "ULT" | "ULE" if s < p:
                return False
            case "SLT" | "SLE":
                p, q = mm_to_signed(width, p, q)
                r, s = mm_to_signed(width, r, s)
                if kind == "SLT" and q < r:
                    return True
                elif kind == "SLE" and q <= r:
                    return True
                elif s < p:
                    return False
                else:
                    pass
            case _:
                pass
        return CmpOp(width, left, right, kind)

    def dump(self, defs: set[str]) -> tuple[str, ...]:
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
        return (
            f"({short}",
            *dump(self.left, defs, self.width),
            *dump(self.right, defs, self.width),
            ")",
        )

    def eval(self, model: Model) -> bool:
        width = self.width
        left, right = eval(self.left, model, width), eval(self.right, model, width)
        match self.kind:
            case "EQ":
                return left == right
            case "ULT":
                return left < right
            case "ULE":
                return left <= right
            case "SLT":
                return to_signed(width, left) < to_signed(width, right)
            case "SLE":
                return to_signed(width, left) <= to_signed(width, right)

    def walk(self) -> Generator[Term]:
        yield from walk(self.left, self.right)

    def substitute(self, subs: dict[str, Term]) -> BooleanTerm:
        return CmpOp.apply(
            self.width,
            _substitute(self.left, subs, self.width),
            _substitute(self.right, subs, self.width),
            self.kind,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class BvShiftOp:
    term: BitvectorTerm
    shift: BitvectorTerm
    way: Literal["L"] | Literal["RU"] | Literal["RS"]
    minmax: tuple[int, int]

    @classmethod
    def apply(
        cls,
        width: int,
        term: BitvectorTerm,
        shift: BitvectorTerm,
        way: Literal["L"] | Literal["RU"] | Literal["RS"],
        recursed: bool = False,
    ) -> BitvectorTerm:
        limit = 1 << width
        match (term, shift, way):
            case _, 0, _:
                return term
            case int(), int(), "L":
                return (term << shift) % limit
            case int(), int(), "RU":
                return term >> shift
            case int(), int(), "RS":
                return to_unsigned(width, to_signed(width, term) >> shift)
            case _, int(), "L" | "RU" if shift >= width:
                return 0
            case ConcatOp(), int(), "L" | "RU" if not recursed:
                terms = list(term.terms)
                while shift >= term.width:
                    terms: list[BitvectorTerm] = (
                        [*terms[1:], 0] if way == "L" else [0, *terms[:-1]]
                    )
                    shift -= term.width
                term = ConcatOp.apply(term.width, *terms)
                if shift:
                    return BvShiftOp.apply(width, term, shift, way, recursed=True)
                return term
            case BvShiftOp(t, s, w), _, _ if w == way:
                return BvShiftOp.apply(width, t, BvAndOp.apply(width, s, shift), way)
            case _:
                m, n = minmax(term, width)
                match way:
                    case "L":
                        if isinstance(shift, int):
                            m = max(m << shift, limit - 1)
                            n = max(n << shift, limit - 1)
                        else:
                            n = limit
                    case "RU":
                        if isinstance(shift, int):
                            m >>= shift
                            n >>= shift
                        else:
                            m = 0
                    case "RS":
                        m, n = 0, limit
                return BvShiftOp(term, shift, way, (m, n))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        match self.way:
            case "L":
                short = "bvshl"
            case "RU":
                short = "bvlshr"
            case "RS":
                short = "bvashr"
        return (
            f"({short}",
            *dump(self.term, defs, width),
            *dump(self.shift, defs, width),
            ")",
        )

    def eval(self, width: int, model: Model) -> int:
        limit = 1 << width
        term, shift = eval(self.term, model, width), eval(self.shift, model, width)
        match self.way:
            case "L":
                return (term << shift) % limit
            case "RU":
                return term >> shift
            case "RS":
                return to_unsigned(width, to_signed(width, term) >> shift)

    def walk(self) -> Generator[Term]:
        yield from walk(self.term, self.shift)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return BvShiftOp.apply(
            width,
            _substitute(self.term, subs, width),
            _substitute(self.shift, subs, width),
            self.way,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class IteOp:
    cond: BooleanTerm
    left: BitvectorTerm
    right: BitvectorTerm
    minmax: tuple[int, int]

    @classmethod
    def apply(
        cls,
        cond: BooleanTerm,
        left: BitvectorTerm,
        right: BitvectorTerm,
        width: int,
    ) -> BitvectorTerm:
        match (cond, left, right):
            case True, _, _:
                return left
            case False, _, _:
                return right
            case _ if left == right:
                return left
            case NotOp(arg), _, _:
                return IteOp.apply(arg, right, left, width)
            case _:
                p, q = minmax(left, width)
                r, s = minmax(right, width)
                return IteOp(cond, left, right, (min(p, r), max(q, s)))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        return (
            "(ite",
            *dump(self.cond, defs),
            *dump(self.left, defs, width),
            *dump(self.right, defs, width),
            ")",
        )

    def eval(self, width: int, model: Model) -> int:
        if eval(self.cond, model):
            return eval(self.left, model, width)
        else:
            return eval(self.right, model, width)

    def walk(self) -> Generator[Term]:
        yield from walk(self.cond, self.left, self.right)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return IteOp.apply(
            _substitute(self.cond, subs),
            _substitute(self.left, subs, width),
            _substitute(self.right, subs, width),
            width,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class ExtractOp:
    term: BitvectorTerm
    prior: int
    minmax: tuple[int, int]

    @classmethod
    def apply(cls, term: BitvectorTerm, rightmost: int, prior: int) -> BitvectorTerm:
        assert rightmost > 0
        mask = (1 << rightmost) - 1
        match (term, rightmost):
            case int(), _:
                return term & mask
            case BvAndOp(m, args), _:
                return BvAndOp.apply(
                    rightmost,
                    m & mask,
                    *(
                        BvAndOp.apply(
                            rightmost, ExtractOp.apply(a, rightmost, prior), mask
                        )
                        for a in args
                    ),
                )
            case BvOrOp(m, args), _:
                return BvOrOp.apply(
                    rightmost,
                    m & mask,
                    *(
                        BvAndOp.apply(
                            rightmost, ExtractOp.apply(a, rightmost, prior), mask
                        )
                        for a in args
                    ),
                )
            case ConcatOp(w, terms), _:
                terms = list(terms)
                while w * len(terms) >= rightmost + w:
                    terms.pop(0)
                term = ConcatOp.apply(w, *terms)
                if w * len(terms) == rightmost:
                    return term
                else:
                    m, n = minmax(term, rightmost)
                    return ExtractOp(term, prior, (m & mask, n & mask))
            case _:
                m, n = minmax(term, rightmost)
                return ExtractOp(term, prior, (m & mask, n & mask))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        return (f"((_ extract {width - 1} 0)", *dump(self.term, defs, self.prior), ")")

    def eval(self, width: int, model: Model) -> int:
        return eval(self.term, model, width) & ((1 << width) - 1)

    def walk(self) -> Generator[Term]:
        yield from walk(self.term)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return ExtractOp.apply(
            _substitute(self.term, subs, self.prior),
            width,
            self.prior,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class ExtendOp:
    term: BitvectorTerm
    extra: int
    signed: bool
    minmax: tuple[int, int]

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
            case ExtendOp(t, x, s), _, _ if s == signed:
                return ExtendOp.apply(width, t, x + extra, signed)
            case _:
                return ExtendOp(term, extra, signed, minmax(term, width))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        inner = dump(self.term, defs, width - self.extra)
        if self.signed:
            return (f"((_ sign_extend {self.extra})", *inner, ")")
        elif "_pretty" in defs:
            match inner:
                case (single,):
                    return (f"...{single}",)
                case _:
                    return ("(...", *inner, ")")
        else:
            return ("(concat", *dump(0, defs, self.extra), *inner, ")")

    def eval(self, width: int, model: Model) -> int:
        if self.signed:
            return to_unsigned(
                width, to_signed(width, eval(self.term, model, width - self.extra))
            )
        else:
            return eval(self.term, model, width - self.extra)

    def walk(self) -> Generator[Term]:
        yield from walk(self.term)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return ExtendOp.apply(
            width - self.extra,
            _substitute(self.term, subs, width - self.extra),
            self.extra,
            self.signed,
        )


@hashcache
@dataclass(frozen=True, slots=True)
class ConcatOp:
    width: int
    terms: tuple[BitvectorTerm, ...]
    minmax: tuple[int, int]

    @classmethod
    def apply(cls, width: int, *terms: BitvectorTerm) -> BitvectorTerm:
        i = 0
        for t in terms:
            if not isinstance(t, int):
                break
            i = (i << width) | t
        else:
            return i
        return ConcatOp(width, terms, (0, (1 << (len(terms) * width)) - 1))

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        r = ["(concat"]
        for t in self.terms:
            r.extend(dump(t, defs, self.width))
        r.append(")")
        return tuple(r)

    def eval(self, width: int, model: Model) -> int:
        i = 0
        for t in self.terms:
            i = (i << self.width) | eval(t, model, self.width)
        return i

    def walk(self) -> Generator[Term]:
        yield from walk(*self.terms)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return ConcatOp.apply(
            self.width,
            *(_substitute(t, subs, self.width) for t in self.terms),
        )


class BitVector[N: int](
    Symbolic, metaclass=abc.ABCMeta if TYPE_CHECKING else BitVectorMeta
):
    __slots__ = ()
    width: Final[int]  # pyright: ignore
    _term: BitvectorTerm

    def __init__(self, value: int | str, /) -> None:
        self._term = value  # pyright: ignore

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({prettify(self._term, self.width)})"

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
            CmpOp.apply(self.width, self._term, other._term, "EQ")
        )

    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: Self, /
    ) -> Constraint:
        assert self.width == other.width
        return Constraint._from_term(
            NotOp.apply(CmpOp.apply(self.width, self._term, other._term, "EQ"))
        )

    def __hash__(self) -> int:
        return self._term.__hash__()


class Uint[N: int](BitVector[N]):
    __slots__ = ()

    def __lt__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._from_term(
            CmpOp.apply(self.width, self._term, other._term, "ULT")
        )

    def __le__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._from_term(
            CmpOp.apply(self.width, self._term, other._term, "ULE")
        )

    def __truediv__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._from_term(
            BvDivOp.apply(self.width, self._term, other._term, False)
        )

    def __mod__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
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

    def __lt__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._from_term(
            CmpOp.apply(self.width, self._term, other._term, "SLT")
        )

    def __le__(self, other: Self, /) -> Constraint:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return Constraint._from_term(
            CmpOp.apply(self.width, self._term, other._term, "SLE")
        )

    def __truediv__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
        assert self.width == other.width
        return self._from_term(BvDivOp.apply(self.width, self._term, other._term, True))

    def __mod__(self, other: Self, /) -> Self:  # pyright: ignore[reportIncompatibleMethodOverride]
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


@hashcache
@dataclass(frozen=True, slots=True)
class UninterpretedTerm:
    name: str
    width: tuple[int, int]

    def dump(self, width: tuple[int, int], defs: set[str]) -> tuple[str, ...]:
        defs.add(
            f"(declare-fun {self.name} () (Array (_ BitVec {width[0]}) (_ BitVec {width[1]})))"
        )
        return (self.name,)

    def eval(self, width: tuple[int, int], model: Model) -> dict[int, int]:
        if self.name in model:
            m = model[self.name]
            assert isinstance(m, dict)
            return m
        else:
            return defaultdict(lambda: 0)

    def walk(self) -> Generator[Term]:
        yield from ()


@hashcache
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

    def dump(self, width: tuple[int, int], defs: set[str]) -> tuple[str, ...]:
        if "_pretty" in defs:
            if isinstance(self.default, UninterpretedTerm):
                stores = [("default", self.default.name)]
            else:
                stores = [("default", " ".join(dump(self.default, defs, width[1])))]
            for k, v in chain(self.base, self.writes):
                stores.append(
                    (
                        " ".join(dump(k, defs, width[0])),
                        " ".join(dump(k, defs, width[1])),
                    )
                )
            return (str(dict(stores)),)
        else:
            if isinstance(self.default, UninterpretedTerm):
                s = dump(self.default, defs, width)
            else:
                s = (
                    f"((as const (Array (_ BitVec {width[0]}) (_ BitVec {width[1]})))",
                    *dump(self.default, defs, width[1]),
                    ")",
                )
            for k, v in chain(self.base, self.writes):
                s = (
                    "(store",
                    *s,
                    *dump(k, defs, width[0]),
                    *dump(v, defs, width[1]),
                    ")",
                )
            return s

    def eval(self, width: tuple[int, int], model: Model) -> dict[int, int]:
        if isinstance(self.default, UninterpretedTerm):
            x = eval(self.default, model, width)
        else:
            d = eval(self.default, model, width[1])
            x = defaultdict[int, int](lambda: d)
        for k, v in chain(self.base, self.writes):
            x[eval(k, model, self.width[0])] = eval(v, model, self.width[1])
        return x

    def walk(self) -> Generator[Term]:
        for k, v in self.writes:
            yield from walk(k, v)
        for _, v in self.base:
            yield from walk(v)
        yield from walk(self.default)


@hashcache
@dataclass(frozen=True, slots=True)
class SelectOp:
    array: ArrayTerm | UninterpretedTerm
    key: BitvectorTerm

    @classmethod
    def apply(cls, array: ArrayTerm, key: BitvectorTerm) -> BitvectorTerm:
        p, q = minmax(key, array.width[0])
        for k, v in reversed(array.writes):
            r, s = minmax(k, array.width[0])
            if key == k:
                return v
            elif not (q < r or s < p):
                break
        else:
            if isinstance(key, int):
                if key in (tmp := dict(array.base)):
                    return tmp[key]
                elif isinstance(array.default, UninterpretedTerm):
                    return SelectOp(array.default, key)
                else:
                    return array.default

        if array.writes or not isinstance(key, int):
            return SelectOp(array, key)
        elif key in (tmp := dict(array.base)):
            return tmp[key]
        elif isinstance(array.default, UninterpretedTerm):
            return SelectOp(array.default, key)
        else:
            return array.default

    def dump(self, width: int, defs: set[str]) -> tuple[str, ...]:
        if "_pretty" in defs:
            return (
                *dump(self.array, defs, self.array.width),
                "[",
                *dump(self.key, defs, self.array.width[0]),
                "]",
            )
        else:
            return (
                "(select",
                *dump(self.array, defs, self.array.width),
                *dump(self.key, defs, self.array.width[0]),
                ")",
            )

    def eval(self, width: int, model: Model) -> int:
        a = eval(self.array, model, self.array.width)
        k = eval(self.key, model, self.array.width[0])
        return a[k]

    def walk(self) -> Generator[Term]:
        yield from walk(self.key, self.array)

    def substitute(self, width: int, subs: dict[str, Term]) -> BitvectorTerm:
        return SelectOp(
            _substitute(self.array, subs, self.array.width),
            _substitute(self.key, subs, width),
        )


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
        return f"{self.__class__.__name__}({prettify(self._array, self._array.width)})"

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
        self._constraint = True
        self._model: Model | str | None = None

    @property
    def constraint(self) -> Constraint:
        return Constraint._from_term(self._constraint)  # pyright: ignore[reportPrivateUsage]

    def add(self, assertion: Constraint, /) -> None:
        self._constraint = AndOp.apply(self._constraint, assertion._term)  # pyright: ignore[reportPrivateUsage]
        self._model = None

    def check(self, *assumptions: Constraint) -> bool:
        aterms = [a._term for a in assumptions]  # pyright: ignore[reportPrivateUsage]
        constraint = reduce(AndOp.apply, aterms, self._constraint)
        self._model = None
        match constraint:
            case bool() as b:
                self._model = {}
                return b
            case str() as s:
                self._model = {s: True}
                return True
            case AndOp():
                args = constraint.args
            case _:
                args = set([constraint])
        asserts = list[str]()
        defs = set[str]()
        for a in args:
            asserts.append(" ".join(dump(a, defs)))
        #     print(prettify(a))
        # print("***")
        smt = "\n".join((*defs, *(f"(assert {s})" for s in asserts), "(check-sat)"))
        p = Popen(["z3", "-model", "/dev/stdin"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        out, err = p.communicate(smt.encode())
        outs = out.decode().split("\n", 1)
        match outs[0]:
            case "sat":
                self._model = outs[1]
                return True
            case "unsat":
                return False
            case _:
                raise RuntimeError(out, err, smt)

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
        assert self._model is not None, "solver is not ready for model evaluation"
        if isinstance(self._model, str):
            tokens = self._model.replace("(", " ( ").replace(")", " ) ").split()
            self._model = {}
            for fun in read_from_tokens(tokens):
                match fun:
                    case "define-fun", name, _, "Bool", value:
                        assert name not in self._model, f"duplicate term: {name}"
                        match value:
                            case "true":
                                self._model[name] = True
                            case "false":
                                self._model[name] = False
                            case _:
                                raise NotImplementedError(f"unknown boolean: {value}")
                    case "define-fun", name, _, [_, "BitVec", _], value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name] = parse_numeral(value)
                    case "define-fun", name, _, ["Array", _, _], value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name] = parse_array(value, self._model)
                    case _:
                        raise NotImplementedError(f"unexpected term: {fun}")
        match sym:
            case Constraint():
                return eval(sym._term, self._model)  # pyright: ignore[reportPrivateUsage]
            case BitVector():
                return eval(sym._term, self._model, sym.width)  # pyright: ignore[reportPrivateUsage]
            case Array():
                return eval(sym._array, self._model, sym._array.width)  # pyright: ignore[reportPrivateUsage]


@overload
def dump(term: BooleanTerm, defs: set[str], width: None = None) -> tuple[str, ...]: ...


@overload
def dump(term: BitvectorTerm, defs: set[str], width: int) -> tuple[str, ...]: ...


@overload
def dump(
    term: ArrayTerm | UninterpretedTerm, defs: set[str], width: tuple[int, int]
) -> tuple[str, ...]: ...


def dump(
    term: Term, defs: set[str], width: None | int | tuple[int, int] = None
) -> tuple[str, ...]:
    match term:
        case True:
            return ("true",)
        case False:
            return ("false",)
        case int():
            assert isinstance(width, int)
            if "_pretty" in defs:
                return (hex(to_signed(width, term)),)
            elif width % 8 == 0:
                return ("#x" + term.to_bytes(width // 8).hex(),)
            else:
                return ("#b" + bin(term)[2:].zfill(width),)
        case str():
            if width is None:
                defs.add(f"(declare-fun {term} () Bool)")
            else:
                defs.add(f"(declare-fun {term} () (_ BitVec {width}))")
            return (term,)
        case _:
            return term.dump(defs) if width is None else term.dump(width, defs)  # pyright: ignore


@overload
def prettify(term: BooleanTerm, width: None = None) -> str: ...


@overload
def prettify(term: BitvectorTerm, width: int) -> str: ...


@overload
def prettify(term: ArrayTerm | UninterpretedTerm, width: tuple[int, int]) -> str: ...


def prettify(term: Term, width: None | int | tuple[int, int] = None) -> str:
    return (
        " ".join(dump(term, set(["_pretty"]), width))  # pyright: ignore
        .replace(" )", ")")
        .replace(" [ ", "[")
        .replace(" ]", "]")
        .replace("... ", "...")
    )


@overload
def eval(term: BooleanTerm, model: Model, width: None = None) -> bool: ...


@overload
def eval(term: BitvectorTerm, model: Model, width: int) -> int: ...


@overload
def eval(
    term: ArrayTerm | UninterpretedTerm,
    model: Model,
    width: tuple[int, int],
) -> dict[int, int]: ...


def eval(
    term: Term, model: Model, width: None | int | tuple[int, int] = None
) -> bool | int | dict[int, int]:
    match term:
        case bool() | int():
            return term
        case str():
            if term in model:
                return model[term]
            match width:
                case None:
                    return True
                case int():
                    return 0
                case (int(), int()):
                    return defaultdict(lambda: 0)
        case _:
            return term.eval(model) if width is None else term.eval(width, model)  # pyright: ignore


def minmax(term: BitvectorTerm, width: int) -> tuple[int, int]:
    match term:
        case int():
            return (term, term)
        case str() | SelectOp():
            return (0, (1 << width) - 1)
        case _:
            return term.minmax


def walk(*terms: Term) -> Generator[Term]:
    for term in terms:
        yield term
        match term:
            case bool() | int() | str():
                pass
            case _:
                yield from term.walk()


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
    raise NotImplementedError("describe")


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return (a.into(Uint257) + b.into(Uint257)).into(Int257) >= Int257(0)


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return a >= b


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
    return ~(a ^ b)


def implies(a: Constraint, b: Constraint) -> Constraint:
    return ~(a & ~b)


def prequal[N: int](a: Uint[N], b: Uint[N]) -> bool:
    return (a == b).reveal() is True


def get_constants(s: Symbolic | Array[Any, Any]) -> set[str]:
    result = set[str]()
    for term in walk(s._term if isinstance(s, Symbolic) else s._array):  # pyright: ignore[reportPrivateUsage]
        match term:
            case str():
                result.add(term)
            case UninterpretedTerm():
                result.add(term.name)
            case _:
                pass
    return result


def substitute[S: Symbolic](s: S, model: dict[str, Symbolic | Array[Any, Any]]) -> S:
    subs = dict[str, Term]()
    for k, v in model.items():
        match v:
            case Symbolic():
                subs[k] = v._term  # pyright: ignore[reportPrivateUsage]
            case Array():
                subs[k] = v._array  # pyright: ignore[reportPrivateUsage]
    match s:
        case Constraint():
            return s._from_term(_substitute(s._term, subs))  # pyright: ignore[reportPrivateUsage]
        case BitVector():
            return s._from_term(_substitute(s._term, subs, s.width))  # pyright: ignore
        case _:
            raise TypeError(f"unhandled type: {s.__class__}")


@overload
def _substitute(
    term: BooleanTerm, subs: dict[str, Term], width: None = None
) -> BooleanTerm: ...


@overload
def _substitute(
    term: BitvectorTerm, subs: dict[str, Term], width: int
) -> BitvectorTerm: ...


@overload
def _substitute[T: ArrayTerm | UninterpretedTerm](
    term: T, subs: dict[str, Term], width: tuple[int, int]
) -> T: ...


def _substitute(
    term: Term, subs: dict[str, Term], width: int | tuple[int, int] | None = None
) -> Term:
    match term:
        case bool() | int():
            return term
        case str():
            if term in subs:
                return subs[term]
            else:
                return term
        case UninterpretedTerm():
            if term.name in subs:
                return subs[term.name]
            else:
                return term
        case _:
            return (
                term.substitute(subs) if width is None else term.substitute(width, subs)  # pyright: ignore
            )


def to_signed(width: int, value: int) -> int:
    if value & (1 << (width - 1)):
        return -((((1 << width) - 1) ^ value) + 1)
    return value


def to_unsigned(width: int, value: int) -> int:
    if value < 0:
        return (((1 << width) - 1) ^ -value) + 1
    return value


def mm_to_signed(width: int, min: int, max: int) -> tuple[int, int]:
    limit = 1 << (width - 1)
    assert 0 <= min <= max < (1 << width)
    if max < limit:  # pos, pos
        return min, max
    elif min >= limit:  # neg, neg
        p, q = to_signed(width, min), to_signed(width, max)
        assert -limit <= p <= q <= 0
        return p, q
    else:  # pos, neg => includes MAX_INT, MIN_INT
        return -limit, limit - 1


def mm_to_unsigned(width: int, min: int, max: int) -> tuple[int, int]:
    limit = 1 << (width - 1)
    assert -limit <= min <= max < limit
    if min >= 0:  # pos, pos
        p, q = min, max
    elif max < 0:  # neg, neg
        p, q = to_unsigned(width, min), to_unsigned(width, max)
    else:  # neg, pos => includes zero, -1
        p, q = 0, (1 << width) - 1
    assert 0 <= p <= q < (1 << width)
    return p, q


def read_from_tokens(tokens: list[str]) -> Any:
    # https://norvig.com/lispy.html
    match tokens.pop(0).strip():
        case "(":
            L = list[Any]()
            while tokens[0] != ")":
                L.append(read_from_tokens(tokens))
            assert tokens.pop(0) == ")"
            return L
        case ")":
            raise SyntaxError("unexpected )")
        case "":
            return None
        case word:
            return word


def parse_numeral(s: str) -> int:
    if s.startswith("#x"):
        return int(s[2:], 16)
    elif s.startswith("#b"):
        return int(s[2:], 2)
    else:
        raise SyntaxError(f"cannot parse numeral: {s}")


def parse_array(parts: str | list[Any], model: Model) -> int | dict[int, int]:
    match parts:
        case str():
            if parts.startswith("#"):
                return parse_numeral(parts)
            else:
                return copy.copy(model[parts])
        case "let", [[name, value]], expr:
            assert name not in model, f"duplicate term: {name}"
            model[name] = parse_array(value, model)
            return parse_array(expr, model)
        case "store", expr, key, value:
            array = parse_array(expr, model)
            assert isinstance(array, dict)
            array[parse_numeral(key)] = parse_numeral(value)
            return array
        case [["as", "const", _], value]:
            default = parse_numeral(value)
            return defaultdict(lambda: default)
        case _:
            raise NotImplementedError(f"unexpected term: {parts}")
