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
from typing import Any, Callable, Iterable, Literal, Self

from . import rewrite, theory_array, theory_bitvec, theory_core
from .rewrite import RewriteMeta
from .theory_bitvec import *
from .theory_core import *

## Code analysis for the rewrite library.

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
NATIVE_WIDTH = 128
ZERO = BValue(0, NATIVE_WIDTH)

MAX_WIDTH = 8

type Vars = tuple[tuple[str, BaseTerm], ...]


class RewriteCase:
    """
    A single case in the term-rewriting match statement.

    In the test suite, we generate RewriteCases at import time (each one turns
    into a test case) so this function should be fast and should not perform
    more validation than needed.
    """

    def __init__(
        self,
        id: str,
        pattern: ast.MatchClass,
        guard: ast.expr | None,
        prefix: list[ast.stmt],
        body: list[ast.stmt],
    ) -> None:
        """Create a new RewriteCase."""
        self.id = id
        self.pattern = pattern
        self.guard = guard
        self.prefix = prefix
        self.body = body

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> Iterable[Self]:
        """Parse the given rewrite function into cases."""
        # Expected function signature: `rewrite(term)`.
        match ast.parse(inspect.getsource(fn)):
            case ast.Module([ast.FunctionDef(_, arguments, fnbody)]):
                pass
            case _:
                raise SyntaxError("unexpected function structure")
        match arguments:
            case ast.arguments([], [ast.arg("term")], None, [], [], None, []):
                pass
            case _:
                raise SyntaxError("rewrite should take a single arg, `term`")

        # Expected function body...
        match fnbody:
            case [
                ast.Expr(ast.Constant(str())),  # docstring
                *prefix,  # variable assignments (optional)
                ast.Match(ast.Name("term"), cases),  # `match term: ...`
            ]:
                pass
            case _:
                raise SyntaxError("rewrite body is malformed")

        # Expected case body: docstring plus a single return statement.
        for case in cases[:-1]:
            match case.body:
                case [ast.Expr(ast.Constant(str() as s)), *body]:
                    id = s.split(":")[0]
                case _:
                    raise SyntaxError("every case should begin with a docstring")
            match case.pattern:
                case ast.MatchClass() as pattern:
                    # Normal single case.
                    yield cls(id, case.pattern, case.guard, prefix, body)
                case ast.MatchOr(patterns):
                    # OR pattern. Split into separate tests.
                    for pattern in patterns:
                        assert isinstance(pattern, ast.MatchClass)
                        yield cls(id, pattern, case.guard, prefix, body)
                case _:
                    raise SyntaxError("malformed case body")

        # Expected final clause: `case _: return term`.
        match cases[-1]:
            case ast.match_case(
                ast.MatchAs(None, None), None, [ast.Return(ast.Name("term"))]
            ):
                pass
            case _:
                raise SyntaxError("final case should be `case _: return term`")


class CaseParser:
    """Handles parsing and validation of a single rewrite case."""

    def __init__(self) -> None:
        """Create a new CaseParser."""
        self.assertions = list[CTerm]()
        self.vars = dict[str, BaseTerm]()

    @classmethod
    def is_equivalent(cls, rw: RewriteCase) -> bool:
        """
        Parse the rewrite case and check its validity.

        Example: `case <pattern> if <guard>: <body>`.
        """
        # 1. Parse the pattern to determine the structure of the input term. In
        #    the process, build up a list of variables bound by the match
        #    statement.
        for term1, vars in cls.match_class(rw.pattern):
            parser = cls()
            for name, value in vars:
                assert name not in parser.vars, "duplicate definition"
                parser.vars[name] = value
            parser.vars["term"] = term1

            # 2. Handle any assignments in the prefix.
            for stmt in rw.prefix:
                match stmt:
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser.pyexpr(expr)
                    case _:
                        raise SyntaxError("expected assignment")

            # 3. Parse the guard, if present. (Relies on vars defined above.)
            if rw.guard is None:
                guard = CValue(True)
            else:
                guard = parser.pyexpr(rw.guard)
            assert isinstance(guard, CTerm)

            # 4. Parse the body. This tells us the value of the rewritten term.
            for stmt in rw.body:
                match stmt:
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser.pyexpr(expr)
                    case ast.Return(ast.expr() as expr):
                        term2 = parser.sexpr(expr)
                        break
                    case _:
                        raise SyntaxError(f"unsupported statement: {stmt}")
            else:
                raise SyntaxError("expected trailing return")

            # 5. Check!
            try:
                goal = Eq(term1, term2)
            except AssertionError:
                continue
            for a in parser.assertions:
                goal = And(goal, a)
            if check(guard, Not(goal)):
                return False
        return True

    @classmethod
    def match(
        cls, pattern: ast.pattern, sort: Sort | None
    ) -> Iterable[tuple[BaseTerm, Vars]]:
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
    ) -> Iterable[tuple[BaseTerm, Vars]]:
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
    def match_class(cls, class_: ast.MatchClass) -> Iterable[tuple[BaseTerm, Vars]]:
        """Parse a MatchClass pattern."""
        assert isinstance(class_.cls, ast.Name)
        name, patterns = class_.cls.id, class_.patterns
        op = Op(name)
        match op.cls:
            case theory_core.CTerm | theory_bitvec.BTerm:
                # Abstract Term, used as a zero-argument type hint in generic
                # ops. Return an anonymous symbol (the caller will add to
                # locals).
                assert len(patterns) == 0
                for sym in op.sort.symbol():
                    yield sym, ()
            case theory_core.CSymbol | theory_bitvec.BSymbol:
                # Symbol. Why would you use this in a rewrite rule?
                raise SyntaxError("Symbol is not supported")
            case theory_core.CValue | theory_bitvec.BValue:
                # Value. Note the scope change: the inner argument, if bound,
                # is a native Python type (NATIVE_WIDTH).
                match patterns:
                    case []:
                        # Anonymous: Value().
                        for sym in op.sort.symbol():
                            yield sym, ()
                    case [ast.MatchSingleton(bool() as b)]:
                        # Concrete: CValue(True).
                        assert op.sort == ConstraintSort
                        yield CValue(b), ()
                    case [ast.MatchValue(ast.Constant(int() as i))]:
                        # Concrete: BValue(0).
                        assert op.sort == BitVectorSort
                        for width in range(1, MAX_WIDTH + 1):
                            yield BValue(i, width), ()
                    case [ast.MatchAs(_, str() as name)]:
                        # Named: Value(a).
                        for sym in op.sort.symbol(name):
                            if isinstance(sym, BTerm):
                                py = ZeroExtend(NATIVE_WIDTH - sym.width, sym)
                                yield sym, ((name, py),)
                            else:
                                yield sym, ((name, sym),)
                    case _:
                        # Unsupported. (Don't try to match on width!)
                        raise SyntaxError(f"unsupported Value(...): {patterns}")
            case _:
                # Operation. Parse type annotations to determine each field's
                # expected sort.
                args = list[Iterable[tuple[BaseTerm | int, Vars]]]()
                for pat, field in zip(patterns, op.fields, strict=True):
                    match field:
                        case "CTerm":
                            arg = cls.match(pat, ConstraintSort)
                        case "BTerm":
                            arg = cls.match(pat, BitVectorSort)
                        case "S":
                            arg = cls.match(pat, None)
                        case "int" | "bool":
                            arg = cls.match_param(pat)
                    args.append(arg)
                for parts in product(*args):
                    terms = list[BaseTerm | int]()
                    vars = list[tuple[str, BaseTerm]]()
                    for term, var in parts:
                        terms.append(term)
                        vars.extend(var)
                    try:
                        yield op.cls(*terms), tuple(vars)
                    except AssertionError:
                        pass

    @classmethod
    def match_param(cls, pattern: ast.pattern) -> Iterable[tuple[int, Vars]]:
        """Parse a match pattern where a param (raw Python int) is expected."""
        match pattern:
            case ast.MatchAs(None, str() as name):
                # AS pattern, e.g. "i" in `ZeroExtend(i, x)`. Enumerate all
                # possibilities.
                for i in range(0, MAX_WIDTH + 1):
                    yield i, ((name, BValue(i, NATIVE_WIDTH)),)
            case ast.MatchValue(ast.Constant(int() as i)):
                # Literal pattern, e.g. "0" in `ZeroExtend(0, x)`.
                yield i, ()
            case _:
                raise SyntaxError(f"unsupported param pattern: {pattern}")

    def pyexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                return self.vars[name]
            case ast.Constant(bool() as b):
                return CValue(b)
            case ast.Constant(int() as i):
                return BValue(i, NATIVE_WIDTH)
            case ast.UnaryOp(op, operand):
                operand = self.pyexpr(operand)
                match op:
                    case ast.Not():
                        assert isinstance(operand, CTerm)
                        return Not(operand)
                    case ast.USub():
                        assert isinstance(operand, BTerm)
                        return Neg(operand)
                    case _:
                        raise SyntaxError(f"unsupported unaryop: {op}")
            case ast.BinOp(left, op, right):
                left, right = self.pyexpr(left), self.pyexpr(right)
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
                        raise SyntaxError(f"unsupported operator: {op}")
            case ast.Compare(left, [op], [right]):
                left, right = self.pyexpr(left), self.pyexpr(right)
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
                        raise SyntaxError(f"unsupported cmpop: {op}")
            case ast.BoolOp(op, values):
                terms = list[CTerm]()
                for v in values:
                    assert isinstance(x := self.pyexpr(v), CTerm)
                    terms.append(x)
                match op:
                    case ast.And():
                        return reduce(And, terms)
                    case ast.Or():
                        return reduce(Or, terms)
                    case _:
                        raise SyntaxError(f"unsupported boolop: {op}")
            case ast.Attribute(ast.Name(name), "sgnd"):
                val = self.vars[name]
                assert isinstance(val, BTerm)
                return SignExtend(NATIVE_WIDTH - val.width, val)
            case ast.Attribute(ast.Name(name), attr):
                val = getattr(self.vars[name], attr)
                assert isinstance(val, int)
                return BValue(val, NATIVE_WIDTH)
            case _:
                raise SyntaxError(f"unsupported pyexpr: {expr}")

    def sexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a symbolic expression."""
        match expr:
            case ast.Name(name):
                return self.vars[name]
            case ast.Call(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.Call(ast.Name("CValue"), [arg]):
                return self.pyexpr(arg)
            case ast.Call(ast.Name("BValue"), [arg, width]):
                inner = self.pyexpr(arg)
                assert isinstance(inner, BTerm)
                width = simplify(self.pyexpr(width))
                # Note that Value(...) converts an inner Python type to an outer
                # symbolic type. We assert that the argument is within range.
                self.assertions.append(
                    Sle(BValue(-(1 << (width - 1)), NATIVE_WIDTH), inner)
                )
                self.assertions.append(
                    Sle(inner, BValue((1 << width) - 1, NATIVE_WIDTH))
                )
                return Extract(width - 1, 0, inner)
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                assert "Value" not in name, "unhandled CValue or BValue"
                op = Op(name)
                res = list[Any]()
                for a, f in zip(args, op.fields, strict=True):
                    if f == "int":
                        res.append(simplify(self.pyexpr(a)))
                    else:
                        res.append(self.sexpr(a))
                return Op(name).cls(*res)
            case _:
                raise SyntaxError(f"unsupported sexpr: {expr}")


def simplify(term: BaseTerm) -> int:
    """Turn a symbolic expression into an integer."""
    match term:
        case BValue(value):
            return value
        case Add(x, y):
            return (simplify(x) + simplify(y)) % (1 << term.width)
        case Sub(x, y):
            return (simplify(x) - simplify(y)) % (1 << term.width)
        case _:
            raise TypeError(f"unable to simplify: {term}")


type Sort = type[ConstraintSort] | type[BitVectorSort]


@dataclass(frozen=True, slots=True)
class ConstraintSort:
    """Represents the boolean sort."""

    @classmethod
    def symbol(cls, name: str | None = None) -> Iterable[CTerm]:
        """Create a Symbol with the given name."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        yield CSymbol(name.encode())


@dataclass(frozen=True, slots=True)
class BitVectorSort:
    """Represents the range of possible BitVector sorts."""

    @classmethod
    def symbol(cls, name: str | None = None) -> Iterable[BTerm]:
        """Create Symbols with the given name, all widths."""
        if name is None:
            name = f"_{randint(0, 2**16)}"
        for width in range(1, MAX_WIDTH + 1):
            yield BSymbol(name.encode(), width)


type Arg = (
    Literal["CTerm"]
    | Literal["BTerm"]
    | Literal["S"]
    | Literal["int"]
    | Literal["bool"]
)


class Op:
    """Represents an SMT operator, with metadata."""

    name: str
    cls: type[BaseTerm]
    fields: tuple[Arg, ...]
    sort: Sort

    def __init__(self, name: str) -> None:
        """Find the Op with the given name."""
        self.name = name

        if hasattr(theory_core, name):
            self.cls = getattr(theory_core, name)
        elif hasattr(theory_bitvec, name):
            self.cls = getattr(theory_bitvec, name)
        else:
            raise KeyError(f"operator not found: {name}")

        args = list[Arg]()
        for name in self.cls.__match_args__:
            typ: str = self.cls.__dataclass_fields__[name].type
            if typ in ("CTerm", "BTerm", "S", "int", "bool"):
                args.append(typ)
            elif typ.startswith("InitVar["):
                pass
            else:
                raise SyntaxError(f"unsupported field type: {typ}")
        self.fields = tuple(args)

        if issubclass(self.cls, CTerm):
            self.sort = ConstraintSort
        elif issubclass(self.cls, BTerm):
            self.sort = BitVectorSort
        else:
            raise TypeError(f"unexpected operator: {self.cls}")


## Code generation for the high-level SMT library, `composite.py`.

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
