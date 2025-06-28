"""A custom SMT solver."""
# ruff: noqa

from __future__ import annotations

import copy
from functools import reduce
from subprocess import Popen, PIPE
from typing import Any, Literal, overload

from smt2 import Array, BitVector, Constraint, Int, Symbolic, Uint
from smt2.composite import ASymbol, And, BSymbol, CSymbol, CTerm, CValue
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


type Tokenized = str | list[Tokenized]


checks = 0


class Solver:
    def __init__(self) -> None:
        self._constraints: list[CTerm] | None = []
        self._model: dict[bytes, Symbolic] | str | None = None

    @property
    def constraint(self) -> Constraint:
        if self._constraints is None:
            return Constraint(False)
        elif not self._constraints:
            return Constraint(True)
        else:
            k = Constraint.__new__(Constraint)
            k._term = reduce(And, self._constraints)  # pyright: ignore[reportPrivateUsage]
            return k

    def add(self, assertion: Constraint, /) -> None:
        self._model = None
        self._add(assertion._term)  # pyright: ignore[reportPrivateUsage]

    def _add(self, term: CTerm, /) -> None:
        if self._constraints is None:
            # This solver is already unsatisfiable.
            return
        elif isinstance(term, And):
            # Lift up And-ed terms for readability.
            self._add(term.left)
            self._add(term.right)
            return
        match term:
            case CValue(True):
                return
            case CValue(False):
                self._constraints = None
            case term:
                self._constraints.append(term)

    def check(self, *assumptions: Constraint) -> bool:
        global checks
        self._model = None
        backup = copy.copy(self._constraints)
        for assumption in assumptions:
            self.add(assumption)
        constraints, self._constraints = self._constraints, backup

        if constraints is None:
            return False
        elif not constraints:
            self._model = {}
            return True

        ctx = DumpContext()
        ctx.walk(*constraints)
        for constraint in constraints:
            ctx.write(b"(assert ")
            constraint.dump(ctx)
            ctx.write(b")\n")
        ctx.write(b"(check-sat)")
        checks += 1

        p = Popen(["bitwuzla", "--print-model"], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        out, err = p.communicate(bytes(ctx.out))
        outs = out.decode().split("\n", 1)
        match outs[0]:
            case "sat":
                self._model = outs[1]
                return True
            case "unsat":
                return False
            case _:
                with open("tmp.smt2", "wb") as f:
                    f.write(ctx.out)
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
            parsed = self._read_from_tokens(tokens)
            assert parsed is not None
            for fun in parsed:
                match fun:
                    case "define-fun", str() as name, _, "Bool", value:
                        assert name not in self._model, f"duplicate term: {name}"
                        match value:
                            case "true":
                                self._model[name.encode()] = Constraint(True)
                            case "false":
                                self._model[name.encode()] = Constraint(False)
                            case _:
                                raise NotImplementedError(f"unknown boolean: {value}")
                    case "define-fun", str() as name, _, [
                        _,
                        "BitVec",
                        _,
                    ], str() as value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name.encode()] = self._parse_numeral(value)
                    case "define-fun", str() as name, _, ["Array", _, _], value:
                        assert name not in self._model, f"duplicate term: {name}"
                        self._model[name.encode()] = self._parse_array(
                            value, self._model
                        )
                    case _:
                        raise NotImplementedError(f"unexpected term: {fun}")
        for k, v in get_symbols(sym).items():
            if k in self._model:
                continue
            elif issubclass(v, Constraint):
                self._model[k] = Constraint(False)
            elif issubclass(v, BitVector):
                self._model[k] = v(0)
            else:
                assert issubclass(v, Array)
                self._model[k] = v(0)
        sym = sym.substitute(self._model)
        assert (r := sym.reveal()) is not None
        return r

    @classmethod
    def _read_from_tokens(cls, tokens: list[str]) -> Tokenized | None:
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
        cls, parts: Tokenized, model: dict[bytes, Symbolic]
    ) -> Uint[Any] | Array[Any, Any]:
        match parts:
            case str():
                if parts.startswith("#"):
                    return cls._parse_numeral(parts)
                else:
                    arr: Any = model[parts.encode()]
                    return copy.deepcopy(arr)
            case "let", [[str() as name, value]], expr:
                assert name not in model, f"duplicate term: {name}"
                model[name.encode()] = cls._parse_array(value, model)
                return cls._parse_array(expr, model)
            case "store", expr, str() as key, str() as value:
                array = cls._parse_array(expr, model)
                assert isinstance(array, Array)
                array[cls._parse_numeral(key)] = cls._parse_numeral(value)
                return array
            case [
                [
                    "as",
                    "const",
                    ["Array", [_, "BitVec", str() as k], [_, "BitVec", str() as v]],
                ],
                str() as default,
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


def get_symbols(s: Symbolic) -> dict[bytes, type[Symbolic]]:
    ctx = DumpContext()
    ctx.walk(s._term)  # pyright: ignore[reportPrivateUsage]
    symbols = dict[bytes, type[Symbolic]]()
    for k, v in ctx.symbols.items():
        match v:
            case CSymbol():
                symbols[k] = Constraint
            case BSymbol():
                symbols[k] = Uint[v.width]
            case ASymbol():
                symbols[k] = Array[Uint[v.key], Uint[v.value]]
            case _:
                raise TypeError(f"unexpected symbol: {v}")
    return symbols


def to_signed(width: int, value: int) -> int:
    if value & (1 << (width - 1)):
        return -((((1 << width) - 1) ^ value) + 1)
    return value


def to_unsigned(width: int, value: int) -> int:
    if value < 0:
        return (((1 << width) - 1) ^ -value) + 1
    return value
