"""Code analysis library for correctness checking."""
# ruff: noqa: F403, F405

from __future__ import annotations

import ast
import inspect
import re
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from random import randint
from subprocess import check_output
from types import ModuleType
from typing import Any, Callable, Generator, Self

from . import rewrite, theory_array, theory_bitvec, theory_core
from .rewrite import RewriteMeta
from .theory_bitvec import *
from .theory_core import *

#
# Code analysis for the rewrite library.
#

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
NATIVE_WIDTH = 128
ZERO = BValue(0, NATIVE_WIDTH)

MAX_WIDTH = 8


class Casette:
    """
    A single case in the term-rewriting match statement.

    In the test suite, we generate Casettes at import time (each one turns into
    a test case) so this function should be fast and not do too much validation.
    """

    def __init__(
        self, case: ast.match_case, prefix: list[ast.stmt], sort: Sort
    ) -> None:
        """Create a new Casette."""
        self.case = case
        self.prefix = prefix
        self.sort = sort
        match case.body:
            case [ast.Expr(ast.Constant(str() as s)), *_]:
                self.id = s.split(":")[0]
            case _:
                raise SyntaxError("every case should begin with a docstring")

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> Generator[Self]:
        """Parse the given rewrite function into cases."""
        # Expected function signature: `rewrite(term: FooTerm) -> FooTerm`.
        match ast.parse(inspect.getsource(fn)):
            case ast.Module([ast.FunctionDef(_, arguments, body)]):
                pass
            case _:
                raise SyntaxError("unexpected function structure")
        match arguments:
            case ast.arguments([], [ast.arg("term")], None, [], [], None, []):
                pass
            case _:
                raise SyntaxError("rewrite should take a single arg, `term`")
        match fn.__annotations__["term"]:
            case "CTerm":
                sort = ConstraintSort
            case "BTerm":
                sort = BitVectorSort
            case typ:
                raise SyntaxError(f"unknown type annotation for `term`: {typ}")

        # Expected body: docstring plus optional variable assignments (to be
        # parsed later), followed by a single `match term`. Each case in the
        # match statement should also begin with a docstring.
        match body[-1]:
            case ast.Match(ast.Name("term"), cases):
                pass
            case _:
                raise SyntaxError("rewrite should end with `match term`")
        for case in cases:
            match case.pattern:
                case ast.MatchOr(patterns):  # split OR patterns into separate tests
                    for pattern in patterns:
                        subcase = ast.match_case(pattern, case.guard, case.body)
                        yield cls(subcase, body[:-1], sort)
                case _:
                    yield cls(case, body[:-1], sort)


type Vars = tuple[tuple[str, BaseTerm], ...]


class CaseParser:
    """Handles parsing and validation of a single rewrite case."""

    def __init__(self) -> None:
        """Create a new CaseParser."""
        self.assertions = list[CTerm]()
        self.vars = dict[str, BaseTerm]()

    @classmethod
    def is_equivalent(cls, casette: Casette) -> bool:
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
        for term1, vars in cls.match(casette.case.pattern, casette.sort):
            parser = cls()
            for name, value in vars:
                assert name not in parser.vars, "duplicate definition"
                parser.vars[name] = value
            parser.vars["term"] = term1

            # 2. Handle any assignments in the prefix.
            for stmt in casette.prefix:
                match stmt:
                    case ast.Expr(ast.Constant(str())):
                        pass  # function docstring, just ignore
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser._pyexpr(expr)
                    case _:
                        raise SyntaxError("expected assignment")

            # 3. Parse the guard, if present. (Relies on vars defined above.)
            if casette.case.guard is None:
                guard = CValue(True)
            else:
                guard = parser._pyexpr(casette.case.guard)
            assert isinstance(guard, CTerm)

            # 4. Parse the body. This tells us the value of the rewritten term.
            for stmt in casette.case.body:
                match stmt:
                    case ast.Expr(ast.Constant(str())):
                        pass  # skip docstring
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser._pyexpr(expr)
                    case ast.Return(ast.expr() as expr):
                        term2 = parser._sexpr(expr)
                        break
                    case _:
                        raise SyntaxError(f"unsupported statement: {stmt}")
            else:
                raise SyntaxError("expected trailing return")

            # 5. Check!
            goal = Eq(term1, term2)
            for a in parser.assertions:
                goal = And(goal, a)
            if check(Not(goal), guard):
                return False
        return True

    @classmethod
    def match(
        cls, pattern: ast.pattern, sort: Sort | None
    ) -> Generator[tuple[BaseTerm, Vars]]:
        """Parse a match pattern of unknown type."""
        match pattern:
            case ast.MatchAs():
                yield from cls.match_as(pattern, sort)
            case ast.MatchClass():
                yield from cls.match_class(pattern)
            case _:
                raise SyntaxError(f"unsupported match pattern: {pattern}")

    @classmethod
    def match_as(
        cls, as_: ast.MatchAs, sort: Sort | None
    ) -> Generator[tuple[BaseTerm, Vars]]:
        """Parse a MatchAs pattern."""
        match (as_.pattern, as_.name):
            case (None, str() as name):
                # Capture pattern, e.g. "x" in `Neg(x)`. Generate a symbol and
                # add to locals.
                assert sort, "capture pattern requires sort"
                for sym in sort.symbol(name):
                    yield sym, ((name, sym),)
            case (ast.MatchClass() as class_, str() as name):
                # AS pattern, e.g. `... as x`. Recurse on subject pattern, then
                # add to locals.
                for sym, vars in cls.match_class(class_):
                    yield sym, (*vars, (name, sym))
            case _, _:
                raise SyntaxError(f"unsupported MatchAs: {as_.pattern} as {as_.name}")

    @classmethod
    def match_class(cls, class_: ast.MatchClass) -> Generator[tuple[BaseTerm, Vars]]:
        """Parse a MatchClass pattern."""
        assert isinstance(class_.cls, ast.Name)
        name, patterns = class_.cls.id, class_.patterns
        match op_and_sort(name):
            case theory_core.CTerm | theory_bitvec.BTerm, sort:
                # Abstract Term, used as a zero-argument type hint in generic
                # ops. Return an anonymous symbol (the caller will add to
                # locals).
                assert len(patterns) == 0
                for sym in sort.symbol():
                    yield sym, ()
            case theory_core.CSymbol | theory_bitvec.BSymbol, sort:
                # Symbol. Why would you use this in a rewrite rule?
                raise SyntaxError("Symbol is not supported")
            case theory_core.CValue | theory_bitvec.BValue, sort:
                # Value. Note the scope change: the inner argument, if bound,
                # is a native Python type (NATIVE_WIDTH).
                match patterns:
                    case []:
                        # Anonymous: Value().
                        for sym in sort.symbol():
                            yield sym, ()
                    case [ast.MatchSingleton(bool() as b)]:
                        # Concrete: CValue(True).
                        assert sort == ConstraintSort
                        yield CValue(b), ()
                    case [ast.MatchValue(ast.Constant(int() as i))]:
                        # Concrete: BValue(0).
                        assert sort == BitVectorSort
                        for width in range(1, MAX_WIDTH + 1):
                            yield BValue(i, width), ()
                    case [ast.MatchAs(_, str() as name)]:
                        # Named: Value(a).
                        for sym in sort.symbol(name):
                            if isinstance(sym, BTerm):
                                sym = ZeroExtend(NATIVE_WIDTH - sym.width, sym)
                            yield sym, ((name, sym),)
                    case _:
                        # Unsupported. (Don't try to match on width!)
                        raise SyntaxError(f"unsupported Value(...): {patterns}")
            case op, sort:
                # Operation. Parse type annotations to determine each field's
                # expected sort.
                args = list[Generator[tuple[BaseTerm, Vars]]]()
                for pat, name in zip(patterns, op.__match_args__, strict=True):
                    match op.__dataclass_fields__[name].type:
                        case "CTerm":
                            arg = cls.match(pat, ConstraintSort)
                        case "BTerm":
                            arg = cls.match(pat, BitVectorSort)
                        case "S":
                            arg = cls.match(pat, None)
                        case "int":
                            raise NotImplementedError
                        case typ:
                            raise SyntaxError(f"unsupported field type: {typ}")
                    args.append(arg)
                for parts in product(*args):
                    terms = list[BaseTerm]()
                    vars = list[tuple[str, BaseTerm]]()
                    for term, var in parts:
                        terms.append(term)
                        vars.extend(var)
                    try:
                        yield op(*terms), tuple(vars)
                    except SortException:
                        pass

    def _pyexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                return self.vars[name]
            case ast.Constant(bool() as b):
                return CValue(b)
            case ast.Constant(int() as i):
                return BValue(i, NATIVE_WIDTH)
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
                        if isinstance(left, BTerm) and left.width < NATIVE_WIDTH:
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
                return SignExtend(NATIVE_WIDTH - val.width, val)
            case ast.Attribute(ast.Name(name), attr):
                val = getattr(self.vars[name], attr)
                assert isinstance(val, int)
                return BValue(val, NATIVE_WIDTH)
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
                self.assertions.append(Ult(inner, BValue(1 << width, NATIVE_WIDTH)))
                return Extract(width - 1, 0, inner)
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                assert "Value" not in name, "unhandled CValue or BValue"
                cls, _ = op_and_sort(name)
                return cls(*(self._sexpr(a) for a in args))
            case _:
                raise NotImplementedError(expr)


type Sort = type[ConstraintSort] | type[BitVectorSort]


@dataclass(frozen=True, slots=True)
class ConstraintSort:
    """Represents the boolean sort."""

    @classmethod
    def symbol(cls, name: str | None = None) -> Generator[CTerm]:
        """Create a Symbol with the given name."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        yield CSymbol(name.encode())

    @classmethod
    def check(cls, kind: str) -> None:
        """Assert that the given Value or Term name matches the sort."""
        assert kind == "CValue" or kind == "CTerm"


@dataclass(frozen=True, slots=True)
class BitVectorSort:
    """Represents the range of possible BitVector sorts."""

    @classmethod
    def symbol(cls, name: str | None = None) -> Generator[BTerm]:
        """Create Symbols with the given name, all widths."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        for width in range(1, MAX_WIDTH + 1):
            yield BSymbol(name.encode(), width)

    @classmethod
    def check(cls, kind: str) -> None:
        """Assert that the given Value or Term name matches the sort."""
        assert kind == "BValue" or kind == "BTerm"


def op_and_sort(name: str) -> tuple[type[BaseTerm], Sort]:
    """Extract the named operator and its sort from the theories."""
    if hasattr(theory_core, name):
        op = getattr(theory_core, name)
    elif hasattr(theory_bitvec, name):
        op = getattr(theory_bitvec, name)
    else:
        raise KeyError(f"operator not found: {name}")

    if issubclass(op, CTerm):
        return op, ConstraintSort
    elif issubclass(op, BTerm):
        return op, BitVectorSort
    else:
        raise TypeError(f"unexpected operator: {op}")


#
# Code generation for the high-level SMT library, `composite.py`.
#

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
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, cast, override

from .theory_core import BaseTerm, DumpContext, SortException


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
