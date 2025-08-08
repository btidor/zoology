"""
Definitions for the core theory.

Up-to-date with SMT-LIB version 2.7.

See: https://smt-lib.org/theories-Core.shtml
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import dataclass, field
from subprocess import PIPE, Popen
from typing import Any, ClassVar, Self, override

from line_profiler import profile
from zbitvector.pybitwuzla import Bitwuzla, BitwuzlaTerm, Kind, Option
from zbitvector.pybitwuzla import Result as Result


@dataclass(repr=False, slots=True, unsafe_hash=True)
class BaseTerm(abc.ABC):
    op: ClassVar[bytes]
    kind: ClassVar[Kind]
    commutative: ClassVar[bool] = False
    count: int = field(init=False, compare=False, default=-1)
    _bzla: BitwuzlaTerm | None = field(init=False, compare=False, default=None)

    # Instances of Symbolic are expected to be immutable:
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def __post_init__(self) -> None:
        pass

    def __repr__(self) -> str:
        ctx = DumpContext()
        self.dump(ctx)
        return ctx.out.decode()

    @abc.abstractmethod
    def sort(self) -> bytes: ...

    @abc.abstractmethod
    def bzla(self) -> BitwuzlaTerm: ...

    @profile
    def rewrite(self) -> BaseTerm:
        return self

    @profile
    def walk(self, ctx: DumpContext) -> None:
        if ctx.visit(self):
            return
        for name in self.__match_args__:
            arg = getattr(self, name, None)
            if isinstance(arg, BaseTerm):
                arg.walk(ctx)

    @profile
    def dump(self, ctx: DumpContext) -> None:
        if ctx.try_alias(self):
            return
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
    visited: dict[int, tuple[int, BaseTerm]] = field(
        default_factory=dict[int, tuple[int, BaseTerm]]
    )
    aliases: dict[int, bytes] = field(default_factory=dict[int, bytes])

    out: bytearray = field(default_factory=bytearray)

    @profile
    def visit(self, term: BaseTerm) -> bool:
        i = id(term)
        if i in self.visited:
            p, q = self.visited[i]
            self.visited[i] = (p + 1, q)
            return True
        else:
            self.visited[i] = (1, term)
            return False

    @profile
    def walk(self, *terms: BaseTerm) -> None:
        for term in terms:
            term.walk(self)
        for name, symbol in self.symbols.items():
            self.write(b"(declare-fun %b () %b)\n" % (name, symbol.sort()))

        queue = list[tuple[int, int, BaseTerm]]()
        for i, (ct, term) in self.visited.items():
            if term.count < 3 or ct * term.count < 64:
                continue
            queue.append((term.count, i, term))
        queue.sort()
        for _, i, term in queue:
            alias = b"_" + hex(i)[2:].encode()
            self.write(b"(define-fun %b () %b " % (alias, term.sort()))
            term.dump(self)
            self.write(b")\n")
            self.aliases[i] = alias

    @profile
    def try_alias(self, term: BaseTerm) -> bool:
        i = id(term)
        if i in self.aliases:
            self.write(self.aliases[i])
            return True
        else:
            return False

    @profile
    def write(self, b: bytes) -> None:
        self.out.extend(b)


def check(*constraints: CTerm) -> bool:
    ctx = DumpContext()
    ctx.walk(*constraints)
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


def make_bitwuzla() -> Bitwuzla:
    bzla = Bitwuzla()
    bzla.set_option(Option.INCREMENTAL, True)
    bzla.set_option(Option.PRODUCE_MODELS, True)
    bzla.set_option(Option.OUTPUT_NUMBER_FORMAT, "hex")
    return bzla


BZLA = make_bitwuzla()
CACHE = dict[bytes, BitwuzlaTerm]()


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CTerm(BaseTerm):
    def sort(self) -> bytes:
        return b"Bool"


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CSymbol(CTerm):
    name: bytes

    @override
    def walk(self, ctx: DumpContext) -> None:
        ctx.symbols[self.name] = self

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(self.name)

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return model.get(self.name, self)

    @override
    def bzla(self) -> BitwuzlaTerm:
        global CACHE
        if self.name not in CACHE:
            CACHE[self.name] = BZLA.mk_const(BZLA.mk_bool_sort(), self.name.decode())
        return CACHE[self.name]


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CValue(CTerm):
    value: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.write(b"true" if self.value else b"false")

    @override
    def substitute(self, model: dict[bytes, BaseTerm]) -> BaseTerm:
        return self

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_bv_value(BZLA.mk_bool_sort(), int(self.value))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Not(CTerm):
    op: ClassVar[bytes] = b"not"
    kind: ClassVar[Kind] = Kind.NOT
    term: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.term.bzla(),))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Implies(CTerm):
    op: ClassVar[bytes] = b"=>"
    kind: ClassVar[Kind] = Kind.IMPLIES
    left: CTerm
    right: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class And(CTerm):
    op: ClassVar[bytes] = b"and"
    kind: ClassVar[Kind] = Kind.AND
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Or(CTerm):
    op: ClassVar[bytes] = b"or"
    kind: ClassVar[Kind] = Kind.OR
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Xor(CTerm):
    op: ClassVar[bytes] = b"xor"
    kind: ClassVar[Kind] = Kind.XOR
    commutative: ClassVar[bool] = True
    left: CTerm
    right: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Eq[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"="
    kind: ClassVar[Kind] = Kind.EQUAL
    commutative: ClassVar[bool] = True
    left: S
    right: S

    @override
    def __post_init__(self) -> None:
        super(Eq, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class Distinct[S: BaseTerm](CTerm):
    op: ClassVar[bytes] = b"distinct"
    kind: ClassVar[Kind] = Kind.DISTINCT
    left: S
    right: S

    @override
    def __post_init__(self) -> None:
        super(Distinct, self).__post_init__()
        assert getattr(self.left, "width", None) == getattr(self.right, "width", None)

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(self.kind, (self.left.bzla(), self.right.bzla()))
        return self._bzla


@dataclass(repr=False, slots=True, unsafe_hash=True)
class CIte(CTerm):
    op: ClassVar[bytes] = b"ite"
    kind: ClassVar[Kind] = Kind.ITE
    cond: CTerm
    left: CTerm
    right: CTerm

    @override
    def bzla(self) -> BitwuzlaTerm:
        if not self._bzla:
            self._bzla = BZLA.mk_term(
                self.kind, (self.cond.bzla(), self.left.bzla(), self.right.bzla())
            )
        return self._bzla
