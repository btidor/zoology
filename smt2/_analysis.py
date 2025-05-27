"""Code analysis."""
# ruff: noqa

from __future__ import annotations

import ast
import copy
import inspect
from typing import Any, Callable, NewType, Self

from ._core import Constraint, Eq, Not, Symbol, Value, __dict__ as coredef

# During analysis, all values are symbolic (type Constraint). This includes
# values that are symbolic at runtime (e.g. Not(...)) and those that are
# instances of concrete Python types (e.g. True). We want to be explicit about
# which context we're operating in, and these type wrappers force us to convert
# between the two explicitly.
SymbolicType = NewType("SymbolicType", Constraint)
PythonType = NewType("PythonType", Constraint)


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
    def __init__(self, pre: PreCase) -> None:
        self.case = pre.case
        self.constraints = list[Constraint]()
        self.svars = dict[str, SymbolicType]()
        self.pyvars = dict[str, PythonType]()
        for stmt in pre.prefix:
            self.assign(stmt)

    def parse_pattern(self) -> list[tuple[Constraint, Self]]:
        match self.case.pattern:
            case ast.MatchAs(None, None):  # terminal `case _:`
                patterns = [ast.MatchAs(None, "term")]
            case ast.MatchOr(patterns):
                pass
            case pattern:
                patterns = [pattern]
        res = list[tuple[Constraint, Self]]()
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
                    ctx.constraints.append(Eq(ctx.sexpr(left), ctx.sexpr(right)))
                case ast.Compare(left, [ast.NotEq()], [right]):
                    # If two trees are unequal, then the symbolic expressions
                    # may be equal or not, we don't know!
                    raise SyntaxError("!= is not supported")
                case other:
                    raise NotImplementedError(other)
            res.append((term, ctx))
        return res

    def parse_body(self) -> Constraint:
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
                self.svars[name] = SymbolicType(Symbol(name.encode()))
                return self.svars[name]
            case ast.MatchClass(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.MatchClass(ast.Name("Value"), patterns):
                match patterns:
                    case [ast.MatchSingleton(bool() as b)]:
                        return SymbolicType(Value(b))
                    case [ast.MatchAs(_, str() as name)]:
                        # Value(...) converts an inner Python type to an outer
                        # symbolic type.
                        assert name not in self.svars
                        self.pyvars[name] = PythonType(Symbol(name.encode()))
                        return SymbolicType(self.pyvars[name])
                    case _:
                        raise TypeError(f"unexpected match on Value(...)", patterns)
            case ast.MatchClass(ast.Name(name), patterns):
                return coredef[name](*(self.match(p) for p in patterns))
            case _:
                raise NotImplementedError(pattern)

    def assign(self, stmt: ast.stmt) -> None:
        match stmt:
            case ast.Assign([ast.Name(name)], expr):
                self.pyvars[name] = self.pyexpr(expr)
            case _:
                raise SyntaxError("expected assignment")

    def sexpr(self, expr: ast.expr) -> SymbolicType:
        match expr:
            case ast.Name(name):
                return self.svars[name]
            case ast.Call(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.Call(ast.Name("Value"), [arg]):
                # Value(...) converts an inner Python type to an outer symbolic
                # type.
                return SymbolicType(self.pyexpr(arg))
            case ast.Call(ast.Name(name), args):  # Not(...), etc.
                return coredef[name](*(self.sexpr(a) for a in args))
            case _:
                raise NotImplementedError(expr)

    def pyexpr(self, expr: ast.expr) -> PythonType:
        match expr:
            case ast.Name(name):
                return self.pyvars[name]
            case ast.Constant(bool() as b):
                return PythonType(Value(b))
            case ast.UnaryOp(op, operand):
                match op:
                    case ast.Not():
                        return PythonType(Not(self.pyexpr(operand)))
                    case _:
                        raise NotImplementedError(op)
            case _:
                raise NotImplementedError(expr)
