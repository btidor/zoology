"""Code analysis."""
# ruff: noqa

from __future__ import annotations

import ast
import copy
import inspect
from typing import Any, Callable, Self

from ._core import Constraint, Eq, Not, Symbol, Value

from smt2 import _core  # pyright: ignore[reportPrivateUsage]


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
        self.vars = dict[str, Constraint]()
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
            subctx = copy.deepcopy(self)  # match() defines new vars!
            term = subctx.match(pattern)
            if subctx.case.guard is not None:
                subctx.constraints.append(subctx.expr(subctx.case.guard))
            res.append((term, subctx))
        return res

    def parse_body(self) -> Constraint:
        for stmt in self.case.body[:-1]:
            self.assign(stmt)
        match self.case.body[-1]:
            case ast.Return(ast.expr() as expr):
                return self.expr(expr)
            case _:
                raise SyntaxError("expected trailing return")

    def match(self, pattern: ast.pattern) -> Constraint:
        match pattern:
            case ast.MatchClass(ast.Name(name), patterns):
                match name:
                    case "Value":
                        assert len(patterns) == 1
                        return self.match(patterns[0])
                    case "Symbol":
                        raise NotImplementedError
                    case _:
                        return _core.__dict__[name](*(self.match(p) for p in patterns))
            case ast.MatchAs(_, str() as name):
                self.vars[name] = Symbol(name.encode())
                return self.vars[name]
            case ast.MatchSingleton(bool() as b):
                return Value(b)
            case ast.MatchSingleton(int() as i):
                raise NotImplementedError(i)
            case ast.MatchValue(value):
                return self.expr(value)
            case _:
                raise TypeError(f"unhandled pattern: {pattern.__class__}")

    def assign(self, stmt: ast.stmt) -> None:
        match stmt:
            case ast.Assign([ast.Name(name)], expr):
                self.vars[name] = self.expr(expr)
            case _:
                raise SyntaxError("expected assignment")

    def expr(self, expr: ast.expr) -> Constraint:
        match expr:
            case ast.UnaryOp(op, operand):
                match op:
                    case ast.Not():
                        return Not(self.expr(operand))
                    case _:
                        raise NotImplementedError(op)
            case ast.Compare(left, [ast.Eq()], [right]):
                # If two trees are equal, then the symbolic expressions must be
                # equal.
                return Eq(self.expr(left), self.expr(right))
            case ast.Compare(left, [ast.NotEq()], [right]):
                # If two trees are unequal, then the symbolic expressions may be
                # equal or not, we don't know!
                raise SyntaxError("!= is not supported")
            case ast.Constant(bool() as b):
                return Value(b)
            case ast.Name(name):
                return self.vars[name]
            case ast.Call(ast.Name(name), args):
                match name:
                    case "Value":
                        assert len(args) == 1
                        return self.expr(args[0])
                    case "Symbol":
                        raise NotImplementedError
                    case _:
                        return _core.__dict__[name](*(self.expr(a) for a in args))
            case _:
                raise NotImplementedError(expr)
