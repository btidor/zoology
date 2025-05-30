"""
Definitions for the core theory.

Up-to-date with SMT-LIB version 2.7.

See: https://smt-lib.org/theories-Core.shtml
"""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass, field
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
            raise RuntimeError(out, err, smt)


@dataclass(frozen=True, slots=True)
class Symbolic(abc.ABC):
    op: ClassVar[bytes]

    # Instances of Symbolic are expected to be immutable:
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    def dump(self, ctx: DumpContext) -> None:
        # 1. Determine Op
        assert self.op
        params = list[bytes]()
        for name in self.__dataclass_fields__.keys():
            v = self.__getattribute__(name)
            if isinstance(v, int):
                params.append(str(v).encode())
        if params:
            ctx.out.extend(b"((_ %b %s)" % (self.op, b" ".join(params)))
        else:
            ctx.out.extend(b"(%b" % self.op)
        # 2. Dump Terms
        for name in self.__dataclass_fields__.keys():
            v = self.__getattribute__(name)
            if isinstance(v, Symbolic):
                ctx.out.extend(b" ")
                v.dump(ctx)
        ctx.out.extend(b")")

    @abc.abstractmethod
    def reveal(self) -> Any: ...


@dataclass(frozen=True, slots=True)
class Constraint(Symbolic):
    def reveal(self) -> bool | None:
        return None


@dataclass(frozen=True, slots=True)
class Symbol(Constraint):
    name: bytes

    @property
    def code(self) -> bytes:
        raise NotImplementedError

    def dump(self, ctx: DumpContext) -> None:
        ctx.add(self.name, (b"(declare-fun %s () Bool)" % self.name))
        ctx.out.extend(self.name)


@dataclass(frozen=True, slots=True)
class Value(Constraint):
    value: bool

    @property
    def code(self) -> bytes:
        raise NotImplementedError

    def dump(self, ctx: DumpContext) -> None:
        ctx.out.extend(b"true" if self.value else b"false")

    @override
    def reveal(self) -> bool | None:
        return self.value


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
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Or(Constraint):
    op: ClassVar[bytes] = b"or"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Xor(Constraint):
    op: ClassVar[bytes] = b"xor"
    left: Constraint
    right: Constraint


@dataclass(frozen=True, slots=True)
class Eq[S: Symbolic](Constraint):
    op: ClassVar[bytes] = b"="
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class Distinct[S: Symbolic](Constraint):
    op: ClassVar[bytes] = b"distinct"
    left: S
    right: S


@dataclass(frozen=True, slots=True)
class Ite(Constraint):
    op: ClassVar[bytes] = b"ite"
    cond: Constraint
    left: Constraint
    right: Constraint
