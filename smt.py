"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

import copy
from functools import reduce
from subprocess import Popen, PIPE
from typing import Any, Literal, overload

from smt2 import Array, Constraint, Int, Model, Symbolic, Uint
from smt2.theory_core import DumpContext


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


class Solver:
    def __init__(self) -> None:
        self._constraint = Constraint(True)
        self._model: Model | str | None = None

    @property
    def constraint(self) -> Constraint:
        return self._constraint

    def add(self, assertion: Constraint, /) -> None:
        self._constraint &= assertion

    def check(self, *assumptions: Constraint) -> bool:
        self._model = None
        constraint = reduce(Constraint.__and__, assumptions, self._constraint)
        if b := constraint.reveal():
            self._model = {}
            return b

        ctx = DumpContext()
        for c in constraint.destructure():
            ctx.write(b"(assert ")
            c.dump(ctx)
            ctx.write(b")\n")
        ctx.write(b"(check-sat)")
        smt = b"\n".join(ctx.defs.values()) + b"\n" + bytes(ctx.out)

        p = Popen(["z3", "-model", "/dev/stdin"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        out, err = p.communicate(smt)
        outs = out.decode().split("\n", 1)
        match outs[0]:
            case "sat":
                self._model = outs[1]
                return True
            case "unsat":
                return False
            case _:
                with open("tmp.smt2", "w") as f:
                    f.write(smt.decode())
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
        assert self._model is not None, "solver is not ready for model evaluation"
        if not isinstance(sym, Array) and (r := sym.reveal()):
            return r
        if isinstance(self._model, str):
            tokens = self._model.replace("(", " ( ").replace(")", " ) ").split()
            self._model = {}
            for fun in self._read_from_tokens(tokens):
                match fun:
                    case "define-fun", name, _, "Bool", value:
                        assert name not in self._model, f"duplicate term: {name}"
                        match value:
                            case "true":
                                self._model[name] = Constraint(True)
                            case "false":
                                self._model[name] = Constraint(False)
                            case _:
                                raise NotImplementedError(f"unknown boolean: {value}")
                    case "define-fun", name, _, [_, "BitVec", _], value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name] = self._parse_numeral(value)
                    case "define-fun", name, _, ["Array", _, _], value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name] = self._parse_array(value, self._model)
                    case _:
                        raise NotImplementedError(f"unexpected term: {fun}")
        sym = sym.substitute(self._model)
        assert (r := sym.reveal()) is not None
        return r

    @classmethod
    def _read_from_tokens(cls, tokens: list[str]) -> Any:
        # https://norvig.com/lispy.html
        match tokens.pop(0).strip():
            case "(":
                L = list[Any]()
                while tokens[0] != ")":
                    L.append(cls._read_from_tokens(tokens))
                assert tokens.pop(0) == ")"
                return L
            case ")":
                raise SyntaxError("unexpected )")
            case "":
                return None
            case word:
                return word

    @classmethod
    def _parse_numeral(cls, s: str) -> Uint[Any]:
        if s.startswith("#x"):
            w = (len(s) - 2) * 4
            return Uint[w](int(s[2:], 16))
        elif s.startswith("#b"):
            w = len(s) - 2
            return Uint[w](int(s[2:], 2))
        else:
            raise SyntaxError(f"cannot parse numeral: {s}")

    @classmethod
    def _parse_array(
        cls, parts: str | list[Any], model: Model
    ) -> Uint[Any] | Array[Any, Any]:
        match parts:
            case str():
                if parts.startswith("#"):
                    return cls._parse_numeral(parts)
                else:
                    assert isinstance(arr := model[parts], Array)
                    return copy.copy(arr)
            case "let", [[name, value]], expr:
                assert name not in model, f"duplicate term: {name}"
                model[name] = cls._parse_array(value, model)
                return cls._parse_array(expr, model)
            case "store", expr, key, value:
                array = cls._parse_array(expr, model)
                assert isinstance(array, Array)
                array[cls._parse_numeral(key)] = cls._parse_numeral(value)
                return array
            case [
                ["as", "const", ["Array", [_, "BitVec", k], [_, "BitVec", v]]],
                default,
            ]:
                default = cls._parse_numeral(default)
                return Array[Uint[int(k)], Uint[int(v)]](default)
            case _:
                raise NotImplementedError(f"unexpected term: {parts}")


def describe[N: int](s: Uint[N]) -> str:
    raise NotImplementedError("describe")


def overflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return (a.into(Uint257) + b.into(Uint257)).into(Int257) >= Int257(0)


def underflow_safe(a: Uint256, b: Uint256) -> Constraint:
    return a >= b


def get_constants(s: Symbolic | Array[Any, Any]) -> set[str]:
    raise NotImplementedError("get_constants")


def substitute[S: Symbolic](s: S, model: dict[str, Symbolic | Array[Any, Any]]) -> S:
    raise NotImplementedError("substitute")


def to_signed(width: int, value: int) -> int:
    if value & (1 << (width - 1)):
        return -((((1 << width) - 1) ^ value) + 1)
    return value


def to_unsigned(width: int, value: int) -> int:
    if value < 0:
        return (((1 << width) - 1) ^ -value) + 1
    return value
