"""Code analysis."""
# ruff: noqa

from __future__ import annotations

import ast
import copy
import inspect
from typing import Any, Callable, NewType, Self

from ._bitvector import BitVector
from ._core import Symbolic, Constraint, Eq, check
from . import _core as core  # pyright: ignore[reportPrivateUsage]
from . import _bitvector as bitvector  # pyright: ignore[reportPrivateUsage]


# During analysis, all values are symbolic (type Constraint, etc.). This
# includes values that are symbolic at runtime (e.g. Not(...)) and those that
# are instances of concrete Python types (e.g. True). We want to be explicit
# about which context we're operating in, and these type wrappers force us to
# convert between the two explicitly.
PythonType = NewType("PythonType", Symbolic)
SymbolicType = NewType("SymbolicType", Symbolic)

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
MAX_WIDTH = 128


class PreCase:
    def __init__(self, case: ast.match_case, prefix: list[ast.stmt]) -> None:
        self.case = case
        self.prefix = prefix

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> list[Self]:
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


class ParsedCase:
    def __init__(self, pre: PreCase, width: int | None) -> None:
        self.case = pre.case
        self.guard = None
        self.assertions = list[Constraint]()
        self.pyvars = dict[str, PythonType]()
        self.svars = dict[str, SymbolicType]()
        self.width = width
        if width is not None:
            assert width < MAX_WIDTH
            self.pyvars["width"] = PythonType(bitvector.Value(width, MAX_WIDTH))
        for stmt in pre.prefix:
            self.assign(stmt)

    def check(self, term1: Symbolic, term2: Symbolic) -> None:
        goal = Eq(term1, term2)
        for a in self.assertions:
            goal = core.And(goal, a)

        if self.guard is None:
            assert not check(core.Not(goal))
        else:
            assert not check(core.Not(goal), self.guard)

    def parse_pattern(self) -> list[tuple[Symbolic, Self]]:
        match self.case.pattern:
            case ast.MatchAs(None, None):  # terminal `case _:`
                patterns = [ast.MatchAs(None, "term")]
            case ast.MatchOr(patterns):
                pass
            case pattern:
                patterns = [pattern]
        res = list[tuple[Symbolic, Self]]()
        for pattern in patterns:
            ctx = copy.deepcopy(self)
            term = ctx.match(pattern)  # may define new vars!
            match ctx.case.guard:
                case None:
                    pass
                case ast.Compare(left, [ast.Eq()], [right]):
                    # If two trees are equal, then the symbolic expressions must
                    # be equal. (Note: this is only safe to do in a guard, not
                    # in the general expr parser).
                    try:
                        ctx.guard = Eq(ctx.sexpr(left), ctx.sexpr(right))
                    except KeyError:
                        # We might want to compare svars or pyvars, but not
                        # both...
                        ctx.guard = Eq(ctx.pyexpr(left), ctx.pyexpr(right))
                case ast.Compare(left, [ast.NotEq()], [right]):
                    # If two trees are unequal, then the symbolic expressions
                    # may be equal or not, we don't know!
                    raise SyntaxError("!= is not supported")
                case other:
                    raise NotImplementedError(other)
            res.append((term, ctx))
        return res

    def parse_body(self) -> Symbolic:
        for stmt in self.case.body[:-1]:
            self.assign(stmt)
        match self.case.body[-1]:
            case ast.Return(ast.expr() as expr):
                return self.sexpr(expr)
            case _:
                raise SyntaxError("expected trailing return")

    def match(self, pattern: ast.pattern) -> SymbolicType:
        match pattern:
            case ast.MatchAs(_, str() as name):
                assert name not in self.pyvars
                if self.width is None:
                    sym = core.Symbol(name.encode())
                else:
                    sym = bitvector.Symbol(name.encode(), self.width)
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
                        return SymbolicType(bitvector.Value(i, self.width))
                    case [ast.MatchAs(_, str() as name)]:
                        # Value(...) converts an inner Python type to an outer
                        # symbolic type.
                        assert name not in self.svars
                        if self.width is None:
                            self.pyvars[name] = PythonType(core.Symbol(name.encode()))
                            return SymbolicType(self.pyvars[name])
                        else:
                            sym = bitvector.Symbol(name.encode(), self.width)
                            self.pyvars[name] = PythonType(
                                bitvector.ZeroExtend[int](MAX_WIDTH - self.width, sym)
                            )
                            return SymbolicType(sym)
                    case _:
                        raise TypeError(f"unexpected match on Value(...)", patterns)
            case ast.MatchClass(ast.Name(name), patterns):
                d = core.__dict__ if self.width is None else bitvector.__dict__
                return d[name](*(self.match(p) for p in patterns))
            case _:
                raise NotImplementedError(pattern)

    def assign(self, stmt: ast.stmt) -> None:
        match stmt:
            case ast.Assign([ast.Name(name)], expr):
                self.pyvars[name] = self.pyexpr(expr)
            case _:
                raise SyntaxError("expected assignment")

    def check_size(self, bv: BitVector[int]) -> Constraint:
        assert self.width is not None
        return bitvector.Ult(
            bv,
            bitvector.Value(1 << self.width, MAX_WIDTH),
        )

    def pyexpr(self, expr: ast.expr) -> PythonType:
        match expr:
            case ast.Name(name):
                return self.pyvars[name]
            case ast.Constant(bool() as b):
                return PythonType(core.Value(b))
            case ast.Constant(int() as i):
                return PythonType(bitvector.Value(i, MAX_WIDTH))
            case ast.UnaryOp(op, operand):
                operand = self.pyexpr(operand)
                match op:
                    case ast.Not():
                        assert isinstance(operand, Constraint)
                        return PythonType(core.Not(operand))
                    case _:
                        raise NotImplementedError(op)
            case ast.BinOp(left, op, right):
                left, right = self.pyexpr(left), self.pyexpr(right)
                assert isinstance(left, BitVector)
                assert isinstance(right, BitVector)
                match op:
                    case ast.Add():
                        return PythonType(bitvector.Add[int](left, right))
                    case ast.Sub():
                        return PythonType(bitvector.Sub[int](left, right))
                    case ast.Mod():
                        return PythonType(bitvector.Smod[int](left, right))
                    case ast.BitAnd():
                        self.assertions.extend(
                            (self.check_size(left), self.check_size(right))
                        )
                        return PythonType(bitvector.And[int](left, right))
                    case ast.BitOr():
                        self.assertions.extend(
                            (self.check_size(left), self.check_size(right))
                        )
                        return PythonType(bitvector.Or[int](left, right))
                    case ast.BitXor():
                        self.assertions.extend(
                            (self.check_size(left), self.check_size(right))
                        )
                        return PythonType(bitvector.Xor[int](left, right))
                    case ast.LShift():
                        self.assertions.extend(
                            (self.check_size(left), self.check_size(right))
                        )
                        return PythonType(bitvector.Shl[int](left, right))
                    case _:
                        raise NotImplementedError(op)
            case _:
                raise NotImplementedError(expr)

    def sexpr(self, expr: ast.expr) -> SymbolicType:
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
                    return SymbolicType(self.pyexpr(args[0]))
                else:
                    assert len(args) == 2
                    # No width-changing operations for now...
                    assert isinstance(args[1], ast.Name) and args[1].id == "width"
                    inner = self.pyexpr(args[0])
                    assert isinstance(inner, BitVector)
                    self.assertions.append(self.check_size(inner))
                    return SymbolicType(
                        bitvector.Extract[int](self.width - 1, 0, inner)
                    )
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                d = core.__dict__ if self.width is None else bitvector.__dict__
                return d[name](*(self.sexpr(a) for a in args))
            case ast.BinOp(a, b, c):
                raise NotImplementedError(a, b, c)
            case _:
                raise NotImplementedError(expr)
