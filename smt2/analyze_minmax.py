"""
Code analysis of the min-max library.

This analyzer uses an SMT solver to check that each min-max rule is correct.
"""
# ruff: noqa: F403, F405

from __future__ import annotations

import ast
import inspect
from typing import Any, Callable, Iterable, Self

from .analyze_rewrite import NATIVE_WIDTH, BitVectorSort, CaseParser
from .theory_bitvec import *
from .theory_core import *


@dataclass
class MinMaxCase:
    """
    A single case in the min-max match statement.

    In the test suite, we generate MinMaxCases at import time (each one turns
    into a test case) so this function should be fast and should not perform
    more validation than needed.
    """

    id: str
    pattern: ast.MatchClass | ast.MatchAs
    guard: ast.expr | None
    prefix: list[ast.stmt]
    body: list[ast.stmt]

    @classmethod
    def from_function(cls, fn: Callable[..., Any]) -> Iterable[Self]:
        """Parse the given minmax function into cases."""
        # Expected function signature: `minmax(term)`.
        match ast.parse(inspect.getsource(fn)):
            case ast.Module([ast.FunctionDef(_, arguments, fnbody)]):
                pass
            case _:
                raise SyntaxError("unexpected function structure")
        match arguments:
            case ast.arguments([], [ast.arg("term")], None, [], [], None, []):
                pass
            case _:
                raise SyntaxError("minmax should take a single arg, `term`")

        # Expected function body...
        match fnbody:
            case [
                ast.Expr(ast.Constant(str())),  # docstring
                *prefix,  # variable assignments (optional)
                ast.Match(ast.Name("term"), cases),  # `match term: ...`
            ]:
                pass
            case _:
                raise SyntaxError("minmax body is malformed")

        # Expected case body: docstring plus a single return statement.
        for case in cases:
            match case.pattern:
                case ast.MatchClass(ast.Name(name)):
                    # Normal single case.
                    yield cls(name, case.pattern, case.guard, prefix, case.body)
                case ast.MatchAs(None, None):
                    # Underscore case (fallthrough).
                    yield cls("_", case.pattern, case.guard, prefix, case.body)
                case _:
                    raise SyntaxError("malformed case body")


class MinMaxCaseParser(CaseParser):
    """Handles parsing and validation of a single min-max case."""

    @classmethod
    def is_sound(cls, mm: MinMaxCase) -> bool:
        """Parse the min-max case and check its validity."""
        # 1. Parse the pattern to determine the structure of the input term. In
        #    the process, build up a list of variables bound by the match
        #    statement.
        for term, vars in cls.match(mm.pattern, BitVectorSort):
            parser = cls()
            preconditions = list[CTerm]()

            # define bounds for each symbolic variable
            for name, sym in vars:
                if not isinstance(sym, BTerm) or sym.width == NATIVE_WIDTH:
                    continue
                min = BSymbol(f"{name}.min".encode(), sym.width)
                max = BSymbol(f"{name}.max".encode(), sym.width)
                parser.vars[f"{name}.min"] = ZeroExtend(NATIVE_WIDTH - sym.width, min)
                parser.vars[f"{name}.max"] = ZeroExtend(NATIVE_WIDTH - sym.width, max)
                preconditions.append(And(Ule(min, sym), Ule(sym, max)))

            # define the constructed input term as "term"
            assert isinstance(term, BTerm)
            vars = (*vars, ("term", term))

            # create a new local scope, add bound variables
            for name, value in vars:
                assert name not in parser.vars, "duplicate definition"
                parser.vars[name] = value

            # 2. Handle any assignments in the prefix.
            for stmt in mm.prefix:
                match stmt:
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser.pyexpr(expr)
                    case _:
                        raise SyntaxError("expected assignment")

            # 3. Parse the guard, if present. (Relies on vars defined above.)
            if mm.guard is not None:
                guard = parser.pyexpr(mm.guard)
                assert isinstance(guard, CTerm)
                preconditions.append(guard)
                if not check(guard):
                    # if the guard is false, don't try to construct the body
                    continue

            # 4. Parse the body. This tells us the value of the rewritten term.
            for stmt in mm.body:
                match stmt:
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser.pyexpr(expr)
                    case ast.Return(ast.Tuple([min, max])):
                        min, max = parser.pyexpr(min), parser.pyexpr(max)
                        assert isinstance(min, BTerm) and isinstance(max, BTerm)
                        break
                    case _:
                        raise SyntaxError(f"unsupported statement: {stmt}")
            else:
                raise SyntaxError("expected trailing return")

            # 5. Check!
            zterm = ZeroExtend(NATIVE_WIDTH - term.width, term)
            goal = And(
                And(Sle(BValue(0, NATIVE_WIDTH), min), Sle(min, zterm)),
                And(Sle(zterm, max), Slt(max, BValue(1 << term.width, NATIVE_WIDTH))),
            )
            goal = reduce(And, parser.assertions, goal)
            if check(*preconditions, Not(goal)):
                return False
        return True
