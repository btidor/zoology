"""Code analysis library for correctness checking."""

from __future__ import annotations

import ast
import copy
import inspect
from random import randint
from typing import Any, Callable, Generator, NewType, Self

from . import bv, core
from .bv import BitVector
from .core import Constraint, Distinct, Eq, Symbolic

# During analysis, all values are symbolic (type Constraint, etc.). This
# includes values that are symbolic at runtime (e.g. Not(...)) and those that
# are instances of concrete Python types (e.g. True). We want to be explicit
# about which context we're operating in, and these type wrappers force us to
# convert between the two explicitly.
PythonType = NewType("PythonType", Symbolic)
SymbolicType = NewType("SymbolicType", Symbolic)

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
MAX_WIDTH = 128


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

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> list[Self]:
        """Parse the given rewrite function into cases."""
        match ast.parse(inspect.getsource(fn)):
            case ast.Module([ast.FunctionDef(_, arguments, body)]):
                pass
            case _:
                raise SyntaxError("unexpected function structure")

        # Assumed function signature: `rewrite(term[, width])`.
        match arguments:
            case ast.arguments([], [ast.arg("term")], None, [], [], None, []):
                pass
            case ast.arguments(
                [], [ast.arg("term"), ast.arg("width")], None, [], [], None, []
            ):
                pass
            case _:
                raise SyntaxError("unexpected function signature")

        # Expected format: zero or more variable assignments (to be parsed
        # later), followed by a single match statement.
        match body[-1]:
            case ast.Match(ast.Name("term"), cases):
                return [cls(c, body[:-1]) for c in cases]
            case _:
                raise SyntaxError("rewrite should end with `match term`")


class CaseParser:
    """Handles parsing and validation of a single rewrite case."""

    def __init__(self, pre: Casette, width: int | None) -> None:
        """Create a new CaseParser."""
        self.assertions = list[Constraint]()
        self.case = pre.case
        self.guard = None
        self.pattern = pre.case.pattern
        self.pyvars = dict[str, PythonType]()
        self.svars = dict[str, SymbolicType]()
        self.width = width

        # For BitVectors, rewrite() takes `width` as its second parameter
        if width is not None:
            assert width < MAX_WIDTH
            self.pyvars["width"] = PythonType(bv.Value(width, MAX_WIDTH))

        # Handle any assignments in the prefix
        for stmt in pre.prefix:
            match stmt:
                case ast.Assign([ast.Name(name)], expr):
                    self.pyvars[name] = self._pyexpr(expr)
                case ast.Expr(ast.Constant(str())):
                    pass  # function docstring, just ignore
                case _:
                    raise SyntaxError("expected assignment")

    def parse_pattern(self) -> Generator[tuple[Symbolic, Self]]:
        """
        Parse the pattern portion of the case statement.

        Example: `case Not(Value(v)): ...`:
        * defines a new bool/int named "v"
        * sets the input (original) term to Not(Symbol("v"))

        In the case of an "or" pattern, multiple terms are returned.
        """
        match self.case.pattern:
            case ast.MatchAs(None, None):  # terminal `case _:`
                patterns = [ast.MatchAs(None, "term")]
            case ast.MatchOr(patterns):
                pass
            case pattern:
                patterns = [pattern]
        for pattern in patterns:
            ctx = copy.deepcopy(self)
            term = ctx._match(pattern)  # may define new vars!
            match ctx.case.guard:
                case None:
                    pass
                case ast.Compare(ast.Name(name), [op], [right]):
                    if name in ctx.svars:
                        # When comparing symbolic expressions: if two ASTs are
                        # equal, the expressions must be equal (but not vice
                        # versa). Note: this rewrite is only safe to do in a
                        # guard.
                        match op:
                            case ast.Eq():
                                ctx.guard = Eq(ctx.svars[name], ctx._sexpr(right))
                            case ast.NotEq():
                                # ASTs distinct: this tells us nothing about
                                # whether or not the expressions are equal.
                                raise SyntaxError(
                                    "symbolic expressions must not be compared with !="
                                )
                            case _:
                                raise NotImplementedError("unsupported op", op)
                    else:
                        # When comparing concrete expressions, treat as normal.
                        ctx.guard = ctx._pyexpr(ctx.case.guard)
                case other:
                    raise NotImplementedError(other)
            yield term, ctx

    def parse_body(self) -> Symbolic:
        """
        Parse the body portion of the case statement.

        Returns a symbolic term representing the value returned from the body,
        i.e. the rewritten term.
        """
        match self.case.body[-1]:
            case ast.Return(ast.expr() as expr):
                return self._sexpr(expr)
            case _:
                raise SyntaxError("expected trailing return")

    def _match(self, pattern: ast.pattern) -> SymbolicType:
        """Recursively parse a case statement pattern."""
        match pattern:
            case ast.MatchAs(_, name):
                if name is None:  # underscore, generate random symbol
                    name = f"_{randint(0, 2**16)}"
                    assert name not in self.svars
                assert name not in self.pyvars
                if self.width is None:
                    sym = core.Symbol(name.encode())
                else:
                    sym = bv.Symbol(name.encode(), self.width)
                self.svars[name] = SymbolicType(sym)
                return self.svars[name]
            case ast.MatchClass(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.MatchClass(ast.Name("Value"), patterns):
                match patterns:
                    case [ast.MatchSingleton(bool() as b)]:
                        return SymbolicType(core.Value(b))
                    case [ast.MatchValue(ast.Constant(int() as i))]:
                        assert self.width is not None
                        assert 0 <= i < (1 << self.width)
                        return SymbolicType(bv.Value(i, self.width))
                    case [ast.MatchAs(_, str() as name)]:
                        # Value(...) converts an inner Python type to an outer
                        # symbolic type.
                        assert name not in self.svars
                        if self.width is None:
                            self.pyvars[name] = PythonType(core.Symbol(name.encode()))
                            return SymbolicType(self.pyvars[name])
                        else:
                            sym = bv.Symbol(name.encode(), self.width)
                            self.pyvars[name] = PythonType(
                                bv.ZeroExtend[int](MAX_WIDTH - self.width, sym)
                            )
                            return SymbolicType(sym)
                    case _:
                        raise TypeError("unexpected match on Value(...)", patterns)
            case ast.MatchClass(ast.Name(name), patterns):
                d = core.__dict__ if self.width is None else bv.__dict__
                return d[name](*(self._match(p) for p in patterns))
            case _:
                raise NotImplementedError(pattern)

    def _check_size(self, x: BitVector[int]) -> Constraint:
        """Assert that a given Python int is within the configured bit-width."""
        assert self.width is not None
        return bv.Ult(x, bv.Value(1 << self.width, MAX_WIDTH))

    def _pyexpr(self, expr: ast.expr) -> PythonType:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                return self.pyvars[name]
            case ast.Constant(bool() as b):
                return PythonType(core.Value(b))
            case ast.Constant(int() as i):
                return PythonType(bv.Value(i, MAX_WIDTH))
            case ast.UnaryOp(op, operand):
                operand = self._pyexpr(operand)
                match op:
                    case ast.Not():
                        assert isinstance(operand, Constraint)
                        return PythonType(core.Not(operand))
                    case _:
                        raise NotImplementedError(op)
            case ast.BinOp(left, op, right):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, BitVector)
                assert isinstance(right, BitVector)
                rnonzero = Distinct(right, bv.Value(0, MAX_WIDTH))
                match op:
                    case ast.Add():
                        return PythonType(bv.Add[int](left, right))
                    case ast.Sub():
                        return PythonType(bv.Sub[int](left, right))
                    case ast.Mult():
                        return PythonType(bv.Mul[int](left, right))
                    case ast.FloorDiv():
                        self.assertions.extend((rnonzero,))  # else ZeroDivisionError
                        return PythonType(bv.Sdiv[int](left, right))
                    case ast.Mod():
                        self.assertions.extend((rnonzero,))  # else ZeroDivisionError
                        return PythonType(bv.Smod[int](left, right))
                    case ast.BitAnd():
                        return PythonType(bv.And[int](left, right))
                    case ast.BitOr():
                        return PythonType(bv.Or[int](left, right))
                    case ast.BitXor():
                        return PythonType(bv.Xor[int](left, right))
                    case ast.LShift():
                        return PythonType(bv.Shl[int](left, right))
                    case _:
                        raise NotImplementedError(op)
            case ast.Compare(left, [op], [right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, BitVector)
                assert isinstance(right, BitVector)
                assert self.width is not None
                match op:
                    case ast.Eq():
                        return PythonType(Eq(left, right))
                    case ast.NotEq():
                        return PythonType(Distinct(left, right))
                    case _:
                        raise NotImplementedError(op)
            case _:
                raise NotImplementedError(expr)

    def _sexpr(self, expr: ast.expr) -> SymbolicType:
        """Recursively parse a symbolic expression."""
        match expr:
            case ast.Name(name):
                return self.svars[name]
            case ast.Call(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.Call(ast.Name("Value"), args):
                # Value(...) converts an inner Python type to an outer symbolic
                # type.
                if self.width is None:
                    assert len(args) == 1
                    return SymbolicType(self._pyexpr(args[0]))
                else:
                    assert len(args) == 2
                    # No width-changing operations for now...
                    assert isinstance(args[1], ast.Name) and args[1].id == "width"
                    inner = self._pyexpr(args[0])
                    assert isinstance(inner, BitVector)
                    self.assertions.append(self._check_size(inner))
                    return SymbolicType(bv.Extract[int](self.width - 1, 0, inner))
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                d = core.__dict__ if self.width is None else bv.__dict__
                return d[name](*(self._sexpr(a) for a in args))
            case ast.BinOp(a, b, c):
                raise NotImplementedError(a, b, c)
            case _:
                raise NotImplementedError(expr)
