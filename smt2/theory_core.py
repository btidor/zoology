"""
Definitions for the core theory.

Up-to-date with SMT-LIB version 2.7.

See: https://smt-lib.org/theories-Core.shtml
"""
# ruff: noqa: D101, D102, D103, D107

from __future__ import annotations

import abc
from dataclasses import dataclass, field
from subprocess import PIPE, Popen
from typing import Any, ClassVar, Iterable, Self, overload, override

from line_profiler import profile
from zbitvector.pybitwuzla import (
    Bitwuzla,
    BitwuzlaSort,
    BitwuzlaTerm,
    Kind,
    Option,
    Result,
)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BaseTerm(abc.ABC):
    op: ClassVar[bytes]
    kind: ClassVar[Kind]
    commutative: ClassVar[bool] = False
    count: int = field(init=False, compare=False)
    _bzla: BitwuzlaTerm | None = field(init=False, compare=False, default=None)
    _pretty: str | None = field(init=False, compare=False, default=None)

    # Instances of Symbolic are expected to be immutable:
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def __post_init__(self) -> None:
        self.count = sum(c.count for c in self.children()) + 1

    def __repr__(self) -> str:
        ctx = DumpContext(pretty=True)
        self.dump(ctx)
        return ctx.out.decode()

    @abc.abstractmethod
    def sort(self) -> bytes: ...

    @abc.abstractmethod
    def children(self) -> Iterable[BaseTerm]: ...

    @property
    def bzla(self) -> BitwuzlaTerm:
        if self._bzla is None:
            self._bzla = self._bzterm()
        return self._bzla

    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_term(self.kind, tuple(t.bzla for t in self.children()))

    @profile
    def rewrite(self) -> BaseTerm:
        return self

    @profile
    def dump(self, ctx: DumpContext) -> None:
        if ctx.pretty and self._pretty:
            raise NotImplementedError
        # 0. Gather Arguments
        args = [getattr(self, name) for name in self.__match_args__]
        params = [str(arg).encode() for arg in args if isinstance(arg, int)]
        terms = [arg for arg in args if isinstance(arg, BaseTerm)]
        # 1. Determine Op
        assert self.op
        if params:
            ctx.write(b"((_ %b %s)" % (self.op, b" ".join(params)))
        else:
            ctx.write(b"(%b" % self.op)
        # 2. Dump Terms
        for term in terms:
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


@dataclass
class DumpContext:
    symbols: dict[bytes, BaseTerm] = field(default_factory=dict[bytes, BaseTerm])
    visited: set[int] = field(default_factory=set[int])

    pretty: bool = field(default=False)
    out: bytearray = field(default_factory=bytearray)

    @profile
    def visit(self, term: BaseTerm) -> bool:
        i = id(term)
        if i in self.visited:
            return True
        else:
            self.visited.add(i)
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


type SortWidth = None | int | tuple[int, int]


class BitwuzlaManager:
    """Manages access to the global Bitwuzla instance."""

    _bzla: Bitwuzla
    _sort: dict[SortWidth, BitwuzlaSort]
    _sym: dict[bytes, tuple[SortWidth, BitwuzlaTerm]]

    # For convenience, centralize all global state here.
    special: dict[Any, Any]  # for CacheMeta
    last_solver: Any  # for Solver

    def __init__(self):
        self._sort = {}
        self._sym = {}
        self.special = {}
        self.last_solver = None
        self.reset()

    def reset(self) -> None:
        self._bzla = Bitwuzla()
        self._bzla.set_option(Option.INCREMENTAL, True)
        self._bzla.set_option(Option.PRODUCE_MODELS, True)
        self._bzla.set_option(Option.OUTPUT_NUMBER_FORMAT, "hex")
        self._sort.clear()
        self._sym.clear()
        self.special.clear()
        self.last_solver = None

    def mk_term(
        self,
        kind: Kind,
        terms: list[BitwuzlaTerm] | tuple[BitwuzlaTerm, ...],
        indices: list[int] | tuple[int, ...] | None = None,
    ) -> BitwuzlaTerm:
        return self._bzla.mk_term(kind, terms, indices)

    def mk_sort(self, width: SortWidth) -> BitwuzlaSort:
        if width not in self._sort:
            match width:
                case None:
                    s = self._bzla.mk_bool_sort()
                case int() as width:
                    s = self._bzla.mk_bv_sort(width)
                case (k, v):
                    s = self._bzla.mk_array_sort(self.mk_sort(k), self.mk_sort(v))
            self._sort[width] = s
        return self._sort[width]

    def mk_symbol(self, name: bytes, width: SortWidth) -> BitwuzlaTerm:
        if name not in self._sym:
            self._sym[name] = (width, self._bzla.mk_const(self.mk_sort(width)))
        orig, term = self._sym[name]
        assert width == orig, f"symbol already used: {name}"
        return term

    @overload
    def mk_value(self, value: bool, width: None) -> BitwuzlaTerm: ...
    @overload
    def mk_value(self, value: int, width: int) -> BitwuzlaTerm: ...
    @overload
    def mk_value(self, value: BitwuzlaTerm, width: tuple[int, int]) -> BitwuzlaTerm: ...
    def mk_value(
        self, value: bool | int | BitwuzlaTerm, width: SortWidth
    ) -> BitwuzlaTerm:
        sort = self.mk_sort(width)
        match width:
            case None:
                assert isinstance(value, bool)
                return self._bzla.mk_bv_value(sort, int(value))
            case int():
                assert isinstance(value, int)
                return self._bzla.mk_bv_value(sort, value)
            case (int(), int()):
                assert isinstance(value, BitwuzlaTerm)
                return self._bzla.mk_const_array(sort, value)

    def check(self, solver: Any, term: BaseTerm) -> bool:
        self.last_solver = solver
        self._bzla.assume_formula(term.bzla)
        match self._bzla.check_sat():
            case Result.SAT:
                return True
            case Result.UNSAT:
                return False
            case Result.UNKNOWN:
                raise RuntimeError

    def get_value_str(self, term: BaseTerm) -> str | dict[str, str]:
        return self._bzla.get_value_str(term.bzla)


BZLA = BitwuzlaManager()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CTerm(BaseTerm):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CSymbol(CTerm):
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
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_symbol(self.name, None)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CValue(CTerm):
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
    def _bzterm(self) -> BitwuzlaTerm:
        return BZLA.mk_value(self.value, None)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    kind: ClassVar[Kind] = Kind.NOT
    term: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.term,)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    kind: ClassVar[Kind] = Kind.IMPLIES
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    kind: ClassVar[Kind] = Kind.AND
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    kind: ClassVar[Kind] = Kind.OR
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    kind: ClassVar[Kind] = Kind.XOR
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    kind: ClassVar[Kind] = Kind.EQUAL
    commutative: ClassVar[bool] = True
    left: S
    right: S

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @override
    def __post_init__(self) -> None:
        super(Eq, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    kind: ClassVar[Kind] = Kind.DISTINCT
    left: S
    right: S

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.left, self.right)

    @override
    def __post_init__(self) -> None:
        super(Distinct, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: CTerm
    right: CTerm

    @override
    def children(self) -> Iterable[BaseTerm]:
        return (self.cond, self.left, self.right)
