"""Code analysis library for correctness checking."""
# ruff: noqa: F403, F405

from __future__ import annotations

import ast
import inspect
import re
from dataclasses import dataclass, fields
from pathlib import Path
from random import randint
from subprocess import check_output
from types import ModuleType
from typing import Any, Callable, Generator, Self

from . import rewrite, theory_array, theory_bitvec, theory_core
from .rewrite import RewriteMeta
from .theory_bitvec import *
from .theory_core import *

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
MAX_WIDTH = 128
ZERO = BValue(0, MAX_WIDTH)


class Casette:
    """
    A single case in the rewrite_*() match statement.

    In the test suite, we generate Casettes at load time (each one turns into a
    test case) -- so this function should be fast and not do too much
    validation.
    """

    def __init__(self, case: ast.match_case, prefix: list[ast.stmt]) -> None:
        """Create a new ThinCase."""
        self.case = case
        self.prefix = prefix
        match case.body:
            case [ast.Expr(ast.Constant(str() as s)), *_]:
                self.id = s.split(":")[0]
            case _:
                raise SyntaxError("every case should begin with a docstring")

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> Generator[Self]:
        """Parse the given rewrite function into cases."""
        match ast.parse(inspect.getsource(fn)):
            case ast.Module([ast.FunctionDef(_, arguments, body)]):
                pass
            case _:
                raise SyntaxError("unexpected function structure")

        # Assumed function signature: `rewrite(term)`.
        match arguments:
            case ast.arguments([], [ast.arg("term")], None, [], [], None, []):
                pass
            case _:
                raise SyntaxError("unexpected function signature")

        # Expected format: zero or more variable assignments (to be parsed
        # later), followed by a single match statement. Each case in the match
        # statement should begin with a docstring.
        match body[-1]:
            case ast.Match(ast.Name("term"), cases):
                pass
            case _:
                raise SyntaxError("rewrite should end with `match term`")

        for case in cases:
            match case.pattern:
                case ast.MatchOr(patterns):  # split or-ed cases into separate tests
                    for pattern in patterns:
                        yield cls(
                            ast.match_case(pattern, case.guard, case.body), body[:-1]
                        )
                case _:
                    yield cls(case, body[:-1])


class CaseParser:
    """Handles parsing and validation of a single rewrite case."""

    def __init__(self, width: int | None) -> None:
        """Create a new CaseParser."""
        self.assertions = list[CTerm]()
        self.vars = dict[str, BaseTerm]()
        self.sort = ConstraintSort() if width is None else BitVectorSort(width)

    def is_equivalent(self, casette: Casette) -> bool:
        """
        Parse the rewrite case and check its validity.

        Example: `case <pattern> if <guard>: <body>`.
        """
        # 1. Parse the pattern (and add vars to local scope). This tells us the
        #    structure of the input term.
        #
        #    Example: `case Not(Value(v)): ...`:
        #    * define a new bool/int named "v"
        #    * return the input (original) term: Not(Symbol("v"))
        #
        term1 = self._match(casette.case.pattern, self.sort)
        self.vars["term"] = term1

        # 1.5. Handle any assignments in the prefix.
        for stmt in casette.prefix:
            match stmt:
                case ast.Expr(ast.Constant(str())):
                    pass  # function docstring, just ignore
                case ast.Assign([ast.Name(name)], expr):
                    self.vars[name] = self._pyexpr(expr)
                case _:
                    raise SyntaxError("expected assignment")

        # 2. Parse the guard, if present. (Relies on vars defined in #1).
        if casette.case.guard is None:
            guard = CValue(True)
        else:
            guard = self._pyexpr(casette.case.guard)
        assert isinstance(guard, CTerm)

        # 3. Parse the body. This tells us the value of the rewritten term.s
        for stmt in casette.case.body:
            match stmt:
                case ast.Expr(ast.Constant(str())):
                    pass  # skip docstring
                case ast.Assign([ast.Name(name)], expr):
                    self.vars[name] = self._pyexpr(expr)
                case ast.Return(ast.expr() as expr):
                    term2 = self._sexpr(expr)
                    break
                case ast.Raise(ast.Name("NotImplementedError")):
                    raise NotImplementedError  # passthrough for unimplemented cases
                case _:
                    raise NotImplementedError("unknown statement", stmt)
        else:
            raise SyntaxError("expected trailing return")

        # 4. Check!
        goal = Eq(term1, term2)
        for a in self.assertions:
            goal = And(goal, a)
        return not check(Not(goal), guard)

    def _match(self, pattern: ast.pattern, sort: Sort) -> BaseTerm:
        """Recursively parse a case statement pattern."""
        match pattern:
            case ast.MatchAs(None, None):
                # Underscore name, e.g. `Ite(_, x, y)`. Generate random label.
                return sort.symbol()
            case (
                ast.MatchAs(None, str() as name)
                | ast.MatchAs(ast.MatchClass(ast.Name("CTerm"), []), str() as name)
                | ast.MatchAs(ast.MatchClass(ast.Name("BTerm"), []), str() as name)
            ):
                # Proper name, e.g. `Neg(x)` (possibly qualified with a simple
                # type). Generate symbol and add to locals.
                self.vars[name] = sort.symbol(name)
                return self.vars[name]
            case ast.MatchAs(cls, str() as name) if cls:
                # Named sub-expression, e.g. `Value(a) as x`. Process as usual,
                # then add to locals.
                self.vars[name] = self._match(cls, sort)
                return self.vars[name]
            case ast.MatchClass(ast.Name(name), patterns):
                # Simple class, e.g. `Not(...)`. Assumed to be from the same
                # theory as the test case.
                return self._match_symbolic(name, patterns, self.sort)
            case _:
                raise NotImplementedError("unsupported pattern", pattern)

    def _match_symbolic(
        self, name: str, patterns: list[ast.pattern], sort: Sort
    ) -> BaseTerm:
        """Parse a symbolic term from a match statement."""
        match name, patterns:
            case "Symbol", _:
                raise SyntaxError("Symbol is not supported")
            case "CValue", [ast.MatchSingleton(bool() as b)]:
                return ConstraintSort().value(b)
            case "BValue", [ast.MatchValue(ast.Constant(int() as i))]:
                assert isinstance(sort, BitVectorSort)
                return sort.value(i)
            case "CValue", [ast.MatchAs(_, str() as name)]:
                # Named value, e.g. `Value(foo)`. Note that `foo` is defined as
                # a Python type, while `Value(foo)` is a symbolic type. We know
                # that `foo` fits in the given width, though.
                assert name not in self.vars, "duplicate name"
                self.vars[name] = ConstraintSort().symbol(name)
                return self.vars[name]
            case "CValue", []:
                # Unnamed value, e.g. `Value() [as bar]`.
                return ConstraintSort().symbol()
            case "BValue", [ast.MatchAs(_, str() as name)]:
                assert isinstance(sort, BitVectorSort)
                assert name not in self.vars, "duplicate name"
                sym = sort.symbol(name)
                self.vars[name] = ZeroExtend(MAX_WIDTH - sort.width, sym)
                return sym
            case "BValue", []:
                assert isinstance(sort, BitVectorSort)
                return sort.symbol()
            case "CValue" | "BValue", [pattern]:
                raise TypeError("unexpected match on Value(...)", pattern)
            case "CValue" | "BValue", _:
                raise TypeError("may only match on single-argument `Value(...)`")
            case _, _:
                # Class from theory, e.g. `Not(...)`. Parse the field
                # annotations to determine the type of the inner expressions.
                cls = operator(name)
                args = list[BaseTerm]()
                filtered = filter(lambda f: f.init and not f.kw_only, fields(cls))
                for field, pattern in zip(filtered, patterns, strict=True):
                    if field.type == "CTerm":
                        arg = self._match(pattern, ConstraintSort())
                    elif field.type == "BTerm":
                        assert isinstance(sort, BitVectorSort)
                        arg = self._match(pattern, sort)
                    elif field.type == "S":
                        # When matching a generic field, check if an explicit
                        # class was given in the case pattern.
                        match pattern:
                            case ast.MatchAs(ast.MatchClass(ast.Name("CTerm"))):
                                arg = self._match(pattern, ConstraintSort())
                            case ast.MatchAs(ast.MatchClass(ast.Name("BTerm"))):
                                assert isinstance(self.sort, BitVectorSort)
                                arg = self._match(pattern, self.sort)
                            case _:
                                arg = self._match(pattern, sort)
                    elif field.type == "int":
                        match pattern:
                            case ast.MatchValue(ast.Constant(k)):
                                arg = k
                            case ast.MatchAs(None, _):
                                raise NotImplementedError("parameterized ops")
                            case _:
                                raise NotImplementedError("unknown constant", pattern)
                    else:
                        raise NotImplementedError("unknown field type", field.type)
                    args.append(arg)
                return cls(*args)

    def _pyexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                return self.vars[name]
            case ast.Constant(bool() as b):
                return CValue(b)
            case ast.Constant(int() as i):
                return BValue(i, MAX_WIDTH)
            case ast.UnaryOp(op, operand):
                operand = self._pyexpr(operand)
                match op:
                    case ast.Not():
                        assert isinstance(operand, CTerm)
                        return Not(operand)
                    case _:
                        raise NotImplementedError(op)
            case ast.BinOp(left, op, right):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, BTerm) and isinstance(right, BTerm)
                rnonzero = Distinct(right, ZERO)
                nonneg = And(Sge(left, ZERO), Sge(right, ZERO))
                match op:
                    case ast.Add():
                        return Add(left, right)
                    case ast.Sub():
                        return Sub(left, right)
                    case ast.Mult():
                        return Mul(left, right)
                    case ast.FloorDiv():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return Sdiv(left, right)
                    case ast.Mod():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return Smod(left, right)
                    case ast.BitAnd():
                        self.assertions.append(nonneg)  # else incorrect result
                        return BAnd(left, right)
                    case ast.BitOr():
                        self.assertions.append(nonneg)  # else incorrect result
                        return BOr(left, right)
                    case ast.BitXor():
                        self.assertions.append(nonneg)  # else incorrect result
                        return BXor(left, right)
                    case ast.LShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return Shl(left, right)
                    case ast.RShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return Lshr(left, right)
                    case _:
                        raise NotImplementedError(op)
            case ast.Compare(left, [op], [right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                match left, op, right:
                    # When comparing symbolic types, (a) if two ASTs are equal,
                    # the expressions must be equal. However, the opposite is
                    # not true! Using != on symbolic types is unsafe because if
                    # two ASTs are distinct, that tells us nothing about whether
                    # or not the expressions are equal.
                    case _, ast.Eq(), _:
                        return Eq(left, right)
                    case _, ast.NotEq(), _:
                        if isinstance(left, BTerm) and left.width < MAX_WIDTH:
                            raise SyntaxError("cannot use != on symbolic types")
                        return Distinct(left, right)
                    case BTerm(), ast.Lt(), BTerm():
                        return Slt(left, right)
                    case BTerm(), ast.LtE(), BTerm():
                        return Sle(left, right)
                    case BTerm(), ast.Gt(), BTerm():
                        return Sgt(left, right)
                    case BTerm(), ast.GtE(), BTerm():
                        return Sge(left, right)
                    case _:
                        raise NotImplementedError(op)
            case ast.BoolOp(op, [left, right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, CTerm) and isinstance(right, CTerm)
                match op:
                    case ast.And():
                        return And(left, right)
                    case ast.Or():
                        return Or(left, right)
                    case _:
                        raise NotImplementedError(op)
            case ast.Attribute(ast.Name(name), "sgnd"):
                val = self.vars[name]
                assert isinstance(val, BTerm)
                return SignExtend(MAX_WIDTH - val.width, val)
            case ast.Attribute(ast.Name(name), attr):
                val = getattr(self.vars[name], attr)
                assert isinstance(val, int)
                return BValue(val, MAX_WIDTH)
            case _:
                raise NotImplementedError(expr)

    def _sexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a symbolic expression."""
        match expr:
            case ast.Name(name):
                return self.vars[name]
            case ast.Call(ast.Name("cast"), [_, arg]):
                return self._sexpr(arg)  # ignore casts
            case ast.Call(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.Call(ast.Name("CValue"), [arg]):
                return self._pyexpr(arg)
            case ast.Call(ast.Name("BValue"), [arg, width]):
                inner = self._pyexpr(arg)
                assert isinstance(inner, BTerm)
                match self._pyexpr(width):
                    case BValue(width):
                        pass
                    case Add(BValue(a), BValue(b)):
                        width = a + b
                    case other:
                        raise NotImplementedError(other)
                # Note that Value(...) converts an inner Python type to an outer
                # symbolic type. We assert that the conversion does not
                # overflow.
                self.assertions.append(Ult(inner, BValue(1 << width, MAX_WIDTH)))
                return Extract(width - 1, 0, inner)
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                assert "Value" not in name, "unhandled CValue or BValue"
                cls = operator(name)
                return cls(*(self._sexpr(a) for a in args))
            case _:
                raise NotImplementedError(expr)


type Sort = ConstraintSort | BitVectorSort[int]


@dataclass(frozen=True, slots=True)
class ConstraintSort:
    """Represents the boolean sort."""

    def symbol(self, name: str | None = None) -> CTerm:
        """Create a Symbol with the given name."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        return CSymbol(name.encode())

    def value(self, val: bool) -> CTerm:
        """Create a concrete Value."""
        return CValue(val)


@dataclass(frozen=True, slots=True)
class BitVectorSort[N: int]:
    """Represents a BitVector sort."""

    width: N

    def symbol(self, name: str | None = None) -> BTerm:
        """Create a Symbol with the given name."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        return BSymbol(name.encode(), self.width)

    def value(self, val: int) -> BTerm:
        """Create a concrete Value."""
        assert 0 <= val < (1 << self.width)
        return BValue(val, self.width)


def operator(name: str) -> Any:
    """Extract the given named operator from the theories."""
    if hasattr(theory_core, name):
        return getattr(theory_core, name)
    elif hasattr(theory_bitvec, name):
        return getattr(theory_bitvec, name)
    else:
        raise KeyError(f"operator not found: {name}")


COMPOSITE_PY = Path(__file__).parent / "composite.py"


class Compositor:
    """Produces a high-level SMT library by composing low-level components."""

    @classmethod
    def dump(cls) -> str:
        """Write out `composite.py`."""
        cls.out = bytearray()
        cls._dump()
        formatted = check_output(["ruff", "format", "-"], input=cls.out)
        return formatted.decode()

    @classmethod
    def _dump(cls) -> None:
        cls.out.extend(b"""\"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analysis

\"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field, fields
from functools import reduce
from typing import Any, ClassVar, cast, override

from .theory_core import BaseTerm, DumpContext


""")
        cls._source(RewriteMeta)
        cls._theory(theory_core)
        cls._theory(theory_bitvec)
        cls._theory(theory_array)
        cls._rewrites(rewrite)

    @classmethod
    def _theory(cls, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isinstance(item, type) or not issubclass(item, BaseTerm):
                continue
            elif item == BaseTerm or inspect.getmodule(item) != module:
                continue
            cls._source(item)

    @classmethod
    def _rewrites(cls, module: ModuleType) -> None:
        for item in vars(module).values():
            if not inspect.isfunction(item) or inspect.getmodule(item) != module:
                continue
            cls._source(item)

    @classmethod
    def _source(cls, object: type | Callable[..., Any]) -> None:
        s = inspect.getsource(object)
        # Inject metaclass for constraints & bitvectors
        s = re.sub(r"(CTerm|BTerm)\(BaseTerm", r"\1(BaseTerm, metaclass=RewriteMeta", s)
        # Delete docstrings, comments
        s = re.sub(r'\n*\s*("""[^"]*"""| #.*)\n+', "\n", s)
        # Skip unimplemented rewrite cases
        s = re.sub(r"\n*\s*case [^_].*\n\s*raise NotImplementedError", "", s)
        cls.out.extend(s.encode())
        cls.out.extend(b"\n")


if __name__ == "__main__":
    with open(COMPOSITE_PY, "w") as f:
        f.write(Compositor().dump())
