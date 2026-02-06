"""
Definitions for the core theory.

Up-to-date with SMT-LIB version 2.7.

See: https://smt-lib.org/theories-Core.shtml
"""
# ruff: noqa: D101, D102, D103, D107

from __future__ import annotations

import abc
from dataclasses import dataclass, field
from enum import Enum
from subprocess import PIPE, Popen
from typing import Any, ClassVar, Iterable, Protocol, Self, TypeVar, override

from line_profiler import profile
from zbitvector.pybitwuzla import (
    BitwuzlaTerm,
    Kind,
)

from .bitwuzla import BZLA

# Type helpers from typeshed-fallback:
_T_co = TypeVar("_T_co", covariant=True)


class SupportsLenAndGetItem(Protocol[_T_co]):
    def __len__(self) -> int: ...
    def __getitem__(self, k: int, /) -> _T_co: ...


def reverse_enumerate[K: Any](
    data: SupportsLenAndGetItem[K],
) -> Iterable[tuple[int, K]]:
    # https://stackoverflow.com/a/390885 (CC BY-SA 2.5)
    for i in range(len(data) - 1, -1, -1):
        yield (i, data[i])


class TermCategory(Enum):
    GENERIC = 0
    VALUE = 1
    SYMBOL = 2
    NOT = 3
    COMMUTATIVE = 4
    MUTABLE = 5


class TermMeta(abc.ABCMeta):
    """Performs term rewriting and caching."""

    @profile
    def __call__(self, *args: Any, recurse: bool = True, cache: bool = True) -> Any:
        """Construct the requested term, then rewrite it."""
        assert issubclass(self, BaseTerm)
        if self.category == TermCategory.COMMUTATIVE:
            assert len(args) == 2
            left, right = args
            if left.category == right.category:
                pass
            elif right.category == TermCategory.VALUE:
                args = (right, left)
            elif left.category == TermCategory.NOT:
                args = (right, left)
        key = (self, *args)
        if self.category != TermCategory.MUTABLE and key in BZLA.argcache and cache:
            return BZLA.argcache[key]
        else:
            term = super(TermMeta, self).__call__(*args)
            if recurse:
                term = term.rewrite()
            if self.category != TermCategory.MUTABLE and cache:
                BZLA.argcache[key] = term
            return term


@dataclass(repr=False, slots=True, eq=False)
class BaseTerm(abc.ABC, metaclass=TermMeta):
    op: ClassVar[bytes]
    kind: ClassVar[Kind]
    category: ClassVar[TermCategory] = TermCategory.GENERIC

    count: int = field(init=False, compare=False)

    _bzla: BitwuzlaTerm | None = field(init=False, compare=False, default=None)
    _pretty: str | None = field(init=False, compare=False, default=None)

    # Instances of BaseTerm are expected to be immutable. This makes copying
    # fast.
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    # Instances of BaseTerm are also expected to be *singletons* (see argcache
    # logic in the metaclass, above). This makes equality fast.
    def __eq__(self, other: Any, /) -> bool:
        return id(self) == id(other)

    def __hash__(self) -> int:
        return id(self) // 16

    def __post_init__(self) -> None:
        self.count = sum(c.count for c in self.children()) + 1

    def __repr__(self) -> str:
        ctx = DumpContext(pretty=True)
        self.dump(ctx)
        return ctx.out.decode()

    @abc.abstractmethod
    def sort(self) -> bytes: ...

    def params(self) -> Iterable[int]:
        return ()

    @abc.abstractmethod
    def children(self) -> Iterable[BaseTerm]: ...

    @property
    def bzla(self) -> BitwuzlaTerm:
        if self._bzla is None:
            leaves = set[BaseTerm]()
            queue = list[BaseTerm]([self])
            while queue:
                term = queue.pop(0)
                if term in leaves:
                    continue
                leaves.add(term)
                queue.extend((t for t in term.children() if t._bzla is None))
            leaves = list(leaves)
            leaves.sort(key=lambda t: t.count)
            for term in leaves:
                term._bzla = term._bzterm()
            assert self._bzla is not None
        return self._bzla

    def _bzterm(self) -> BitwuzlaTerm:
        params = tuple(self.params())
        return BZLA.mk_term(
            self.kind,
            tuple(t.bzla for t in self.children()),
            params if params else None,
        )

    def rewrite(self) -> BaseTerm:
        return self

    @profile
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty and self._pretty:
            raise NotImplementedError
        # 1. Determine Op
        assert self.op
        if params := tuple(self.params()):
            ctx.write(
                b"((_ %b %b)" % (self.op, b" ".join(str(p).encode() for p in params))
            )
        else:
            ctx.write(b"(%b" % self.op)
        # 2. Dump Terms
        for term in self.children():
            ctx.write(b" ")
            term.dump(ctx)
        ctx.write(b")")

    @profile
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        args = list[Any]()
        for name in self.__match_args__:
            arg = getattr(self, name)
            if isinstance(arg, BaseTerm):
                args.append(arg.substitute(model))
            elif isinstance(arg, tuple):
                s = list[BaseTerm | tuple[BaseTerm, ...]]()
                for a in arg:  # pyright: ignore[reportUnknownVariableType]
                    match a:
                        case BaseTerm():
                            s.append(a.substitute(model))
                        case tuple():
                            t = list[BaseTerm]()
                            for b in a:  # pyright: ignore[reportUnknownVariableType]
                                assert isinstance(b, BaseTerm)
                                t.append(b.substitute(model))
                            s.append(tuple(t))
                        case other:  # pyright: ignore[reportUnknownVariableType]
                            raise TypeError(f"unexpected arg: {other}")
                args.append(tuple(s))
            else:
                args.append(arg)
        return self.__class__(*args)

    @profile
    def replace(
        self, model: dict[BaseTerm, BaseTerm], cache: dict[BaseTerm, BaseTerm]
    ) -> BaseTerm:
        if (r := model.get(self)) is not None:
            return r
        elif (r := cache.get(self)) is not None:
            return r
        args = list[Any]()
        for name in self.__match_args__:
            arg = getattr(self, name)
            if isinstance(arg, BaseTerm):
                args.append(arg.replace(model, cache))
            elif isinstance(arg, tuple):
                s = list[BaseTerm | tuple[BaseTerm, ...]]()
                for a in arg:  # pyright: ignore[reportUnknownVariableType]
                    match a:
                        case BaseTerm():
                            s.append(a.replace(model, cache))
                        case tuple():
                            t = list[BaseTerm]()
                            for b in a:  # pyright: ignore[reportUnknownVariableType]
                                assert isinstance(b, BaseTerm)
                                t.append(b.replace(model, cache))
                            s.append(tuple(t))
                        case other:  # pyright: ignore[reportUnknownVariableType]
                            raise TypeError(f"unexpected arg: {other}")
                args.append(tuple(s))
            else:
                args.append(arg)
        cache[self] = self.__class__(*args)
        return cache[self]


@dataclass
class DumpContext:
    symbols: dict[bytes, BaseTerm] = field(default_factory=dict[bytes, BaseTerm])
    visited: set[BaseTerm] = field(default_factory=set[BaseTerm])

    pretty: bool = field(default=False)
    out: bytearray = field(default_factory=bytearray)

    @profile
    def visit(self, term: BaseTerm) -> bool:
        if term in self.visited:
            return True
        else:
            self.visited.add(term)
            return False

    @profile
    def prepare(self, *terms: BaseTerm) -> None:
        queue = list[BaseTerm](terms)
        visited = set[BaseTerm]()
        while queue:
            term = queue.pop()
            if term in visited:
                continue
            if (s := getattr(term, "name", None)) is not None:
                self.symbols[s] = term
            queue.extend(term.children())
            visited.add(term)
        for name, symbol in self.symbols.items():
            self.write(b"(declare-fun %b () %b)\n" % (name, symbol.sort()))

    @profile
    def write(self, b: bytes) -> None:
        self.out.extend(b)


def check(*constraints: CTerm) -> bool:
    ctx = DumpContext()
    ctx.prepare(*constraints)
    for constraint in constraints:
        ctx.write(b"(assert ")
        constraint.dump(ctx)
        ctx.write(b")\n")
    ctx.write(b"(check-sat)")

    print(ctx.out.decode())
    p = Popen(["bitwuzla", "--print-model"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    out, err = p.communicate(bytes(ctx.out))
    outs = out.decode().split("\n", 1)
    match outs[0]:
        case "sat":
            return True
        case "unsat":
            return False
        case _:
            raise RuntimeError(out, err)


@dataclass(repr=False, slots=True, eq=False)
class CTerm(BaseTerm):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(repr=False, slots=True, eq=False)
class CSymbol(CTerm):
    category: ClassVar[TermCategory] = TermCategory.SYMBOL
    name: bytes

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def replace(
        self, model: dict[BaseTerm, BaseTerm], cache: dict[BaseTerm, BaseTerm]
    ) -> BaseTerm:
        if (r := model.get(self)) is not None:
            return r
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, None)


@dataclass(repr=False, slots=True, eq=False)
class CValue(CTerm):
    category: ClassVar[TermCategory] = TermCategory.VALUE
    value: bool

    @override
    def children(self) -> Iterable[BaseTerm]:
        return ()

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def replace(
        self, model: dict[BaseTerm, BaseTerm], cache: dict[BaseTerm, BaseTerm]
    ) -> BaseTerm:
        if (r := model.get(self)) is not None:
            return r
        return self

    @override
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.value, None)


@dataclass(repr=False, slots=True, eq=False)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    kind: ClassVar[Kind] = Kind.NOT
    category: ClassVar[TermCategory] = TermCategory.NOT
    term: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, eq=False)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    kind: ClassVar[Kind] = Kind.IMPLIES
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, eq=False)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    kind: ClassVar[Kind] = Kind.AND
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, eq=False)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    kind: ClassVar[Kind] = Kind.OR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, eq=False)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    kind: ClassVar[Kind] = Kind.XOR
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, eq=False)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    kind: ClassVar[Kind] = Kind.EQUAL
    category: ClassVar[TermCategory] = TermCategory.COMMUTATIVE
    left: S
    right: S

    @override
    def children(self) -> Iterable[S]:
        return (self.left, self.right)

    @override
    def __post_init__(self) -> None:
        super(Eq, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(repr=False, slots=True, eq=False)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    kind: ClassVar[Kind] = Kind.DISTINCT
    left: S
    right: S

    @override
    def children(self) -> Iterable[S]:
        return (self.left, self.right)

    @override
    def __post_init__(self) -> None:
        super(Distinct, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(repr=False, slots=True, eq=False)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[CTerm]:
        return (self.cond, self.left, self.right)
