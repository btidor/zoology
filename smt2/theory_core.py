"""
Definitions for the core theory.

Up-to-date with SMT-LIB version 2.7.

See: https://smt-lib.org/theories-Core.shtml
"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import dataclass, field, fields
from subprocess import PIPE, Popen
from typing import Any, ClassVar, Self, override


@dataclass
class DumpContext:
    out: bytearray = field(default_factory=bytearray)
    defs: dict[bytes, bytes] = field(default_factory=dict[bytes, bytes])

    def add(self, name: bytes, defn: bytes) -> None:
        if name in self.defs:
            assert self.defs[name] == defn
        else:
            self.defs[name] = defn

    def write(self, b: bytes) -> None:
        self.out.extend(b)


def check(*constraints: Constraint) -> bool:
    ctx = DumpContext()
    for constraint in constraints:
        ctx.write(b"(assert ")
        constraint.dump(ctx)
        ctx.write(b")\n")
    ctx.write(b"(check-sat)")

    smt = b"\n".join(ctx.defs.values()) + b"\n" + ctx.out
    print(smt.decode())
    p = Popen(["z3", "-model", "/dev/stdin"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
    out, err = p.communicate(smt)
    outs = out.decode().split("\n", 1)
    match outs[0]:
        case "sat":
            return True
        case "unsat":
            return False
        case _:
            print(smt)
            raise RuntimeError(out, err)


@dataclass(frozen=True, slots=True)
class Base(abc.ABC):
    op: ClassVar[bytes]
    commutative: ClassVar[bool] = False

    # Instances of Symbolic are expected to be immutable:
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def dump(self, ctx: DumpContext) -> None:
        # 0. Gather Arguments
        params = list[bytes]()
        terms = list[Base]()
        for fld in fields(self):
            if not fld.init or fld.kw_only:
                continue
            v = getattr(self, fld.name)
            if isinstance(v, int):
                params.append(str(v).encode())
            elif isinstance(v, Base):
                terms.append(v)
        # 1. Determine Op
        assert self.op
        if params:
            ctx.out.extend(b"((_ %b %s)" % (self.op, b" ".join(params)))
        else:
            ctx.out.extend(b"(%b" % self.op)
        # 2. Dump Terms
        for term in terms:
            ctx.out.extend(b" ")
            term.dump(ctx)
        ctx.out.extend(b")")


@dataclass(frozen=True, slots=True)
class Constraint(Base): ...


@dataclass(frozen=True, slots=True)
class CSymbol(Constraint):
    name: bytes

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.out.extend(self.name)


@dataclass(frozen=True, slots=True)
class CValue(Constraint):
    value: bool

    @override
    def dump(self, ctx: DumpContext) -> None:
        ctx.out.extend(b"true" if self.value else b"false")


@dataclass(frozen=True, slots=True)
class Not(Constraint):
    op: ClassVar[bytes] = b"not"
    term: Constraint


@dataclass(frozen=True, slots=True)
class Implies(Constraint):
    op: ClassVar[bytes] = b"=>"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class And(Constraint):
    op: ClassVar[bytes] = b"and"
    commutative: ClassVar[bool] = True
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Or(Constraint):
    op: ClassVar[bytes] = b"or"
    commutative: ClassVar[bool] = True
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Xor(Constraint):
    op: ClassVar[bytes] = b"xor"
    commutative: ClassVar[bool] = True
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Eq[S: Base](Constraint):
    op: ClassVar[bytes] = b"="
    commutative: ClassVar[bool] = True
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class Distinct[S: Base](Constraint):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class CIte(Constraint):
    op: ClassVar[bytes] = b"ite"
    cond: Constraint
    left: Constraint
    right: Constraint
