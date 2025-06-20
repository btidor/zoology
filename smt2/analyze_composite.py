"""
Code generation for the composite SMT library.

Takes the low-level library defined in `theory_*.py`, combines it with the rules
from the rewrite library, and outputs to `composite.py`.
"""

from __future__ import annotations

import ast
from bisect import insort
from inspect import getmodule, getsource, isfunction
from pathlib import Path
from subprocess import check_output
from types import ModuleType
from typing import Any, Callable

from . import rewrite, theory_array, theory_bitvec, theory_core
from .analyze_minmax import MinMaxCase
from .minmax import RewriteMeta, constraint_minmax, propagate_minmax
from .theory_core import BaseTerm

COMPOSITE_PY = Path(__file__).parent / "composite.py"


class Compositor:
    """Produces a high-level SMT library by composing low-level components."""

    def __init__(self) -> None:
        """Create a new Compositor."""
        self.out = bytearray()
        self.mmcases = {
            case.id: case for case in MinMaxCase.from_function(propagate_minmax)
        }

    def dump(self) -> bytes:
        """Write out `composite.py`."""
        assert len(self.out) == 0
        self.out.extend(b"""\"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analyze_composite

\"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
import copy
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, Self, override

from .theory_core import BaseTerm, DumpContext

type MinMax = tuple[int, int]

""")
        self._source(RewriteMeta)
        self._theory(theory_core)
        self._theory(theory_bitvec)
        self._theory(theory_array)
        self._rewrites(rewrite)
        self._source(constraint_minmax)
        return check_output(["ruff", "format", "-"], input=self.out)

    def _theory(self, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isinstance(item, type) or not issubclass(item, BaseTerm):
                continue
            elif item == BaseTerm or getmodule(item) != module:
                continue
            match ast.parse(getsource(item)).body:
                case [ast.ClassDef("BTerm" | "CTerm") as cls]:
                    # inject metaclass for constraints & bitvectors
                    cls.keywords.append(
                        ast.keyword("metaclass", ast.Name("RewriteMeta"))
                    )
                case [ast.ClassDef() as cls]:
                    pass
                case _:
                    raise SyntaxError("unexpected item in theory")

            # Have BTerm set min, max by default.
            if item == theory_bitvec.BTerm:
                self._post_init_append(cls, *self._minmax(cls, item, self.mmcases["_"]))
            elif item.__name__ in self.mmcases:
                self._post_init_append(
                    cls, *self._minmax(cls, item, self.mmcases[item.__name__])
                )
            self._source(cls)

    def _rewrites(self, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isfunction(item) or getmodule(item) != module:
                continue
            self._source(item)

    def _setattr(self, name: str, expr: ast.expr) -> ast.stmt:
        return ast.Expr(
            ast.Call(
                ast.Attribute(ast.Name("object"), "__setattr__"),
                [ast.Name("self"), ast.Constant(name), expr],
            )
        )

    def _post_init_append(self, cls: ast.ClassDef, *stmts: ast.stmt) -> None:
        for node in ast.walk(cls):
            match node:
                case ast.FunctionDef("__post_init__"):
                    node.body.extend(stmts)
                    return
                case _:
                    pass

        supercall = ast.Call(
            ast.Attribute(
                ast.Call(ast.Name("super"), [ast.Name(cls.name), ast.Name("self")]),
                "__post_init__",
            )
        )
        fn = ast.FunctionDef(
            "__post_init__",
            ast.arguments([], [ast.arg("self")]),
            [ast.Expr(supercall), *stmts],
            [],
            ast.Constant(None),
        )
        insort(cls.body, fn, key=lambda s: isinstance(s, ast.FunctionDef))

    def _minmax(
        self, cls: ast.ClassDef, item: type[BaseTerm], case: MinMaxCase
    ) -> list[ast.stmt]:
        # Parse variable assignments from the prefix.
        replacer = ReplaceVariables({"term": ast.Name("self")})
        for stmt in case.prefix:
            match stmt:
                case ast.Assign([ast.Name(name)], expr):
                    replacer.vars[name] = replacer.visit(expr)
                case _:
                    raise SyntaxError("malformed minmax prefix")
        # Parse match case.
        match case.pattern:
            case ast.MatchClass(ast.Name(op), args):
                assert op == cls.name
            case ast.MatchAs(None, None):
                args = []
            case _:
                raise SyntaxError("malformed minmax case pattern")
        conds = list[ast.expr]()
        for arg, field in zip(args, item.__match_args__):
            accessor = ast.Attribute(ast.Name("self"), field)
            match arg:
                case ast.MatchAs(None, None):
                    # Wildcard pattern, i.e. `_`.
                    pass
                case ast.MatchAs(None, str() as name):
                    # Capture pattern, e.g. "x" in `Neg(x)`. Add name to
                    # replacements.
                    replacer.vars[name] = accessor
                case ast.MatchAs(ast.MatchClass(ast.Name("BValue"), []), name):
                    # AS pattern, i.e. `BValue() as x`.
                    if name:
                        replacer.vars[name] = accessor
                    conds.append(
                        ast.Call(ast.Name("isinstance"), [accessor, ast.Name("BValue")])
                    )
                case ast.MatchClass(
                    ast.Name("BValue"), [ast.MatchAs(None, str() as name)]
                ):
                    # AS pattern, i.e. `BValue(a)`.
                    replacer.vars[name] = ast.Attribute(accessor, "value")
                    conds.append(
                        ast.Call(ast.Name("isinstance"), [accessor, ast.Name("BValue")])
                    )
                case ast.MatchSequence(
                    [
                        ast.MatchClass(
                            ast.Name("BValue"), [ast.MatchAs(None, str() as left)]
                        ),
                        ast.MatchAs(None, str() as right),
                    ]
                ):
                    # Tuple, special-cased for Concat.
                    aleft = ast.Subscript(accessor, ast.Constant(0))
                    replacer.vars[left] = ast.Attribute(aleft, "value")
                    conds.append(
                        ast.Compare(
                            ast.Call(ast.Name("len"), [accessor]),
                            [ast.Eq()],
                            [ast.Constant(2)],
                        )
                    )
                    conds.append(
                        ast.Call(ast.Name("isinstance"), [aleft, ast.Name("BValue")])
                    )
                    replacer.vars[right] = ast.Subscript(accessor, ast.Constant(1))
                case _:
                    raise SyntaxError("unexpected match pattern")

        # Parse guard, if present.
        match case.guard:
            case None:
                pass
            case ast.BoolOp(ast.And(), expr):
                conds.extend(expr)
            case _:
                conds.append(case.guard)

        # Parse return statement, translate into code.
        match case.body:
            case [ast.Return(ast.Tuple([min, max]))]:
                pass
            case _:
                raise SyntaxError("malformed minmax case body")
        stmt = [
            self._setattr("min", replacer.visit(min)),
            self._setattr("max", replacer.visit(max)),
        ]
        if conds:
            conds = [replacer.visit(c) for c in conds]
            return [ast.If(ast.BoolOp(ast.And(), conds), stmt)]
        else:
            return stmt

    def _source(self, object: type | Callable[..., Any] | ast.stmt) -> None:
        if not isinstance(object, ast.stmt):
            # Round-trip to delete comments.
            p = ast.parse(getsource(object))
            assert len(p.body) == 1
            stmt = p.body[0]
        else:
            stmt = object
        stmt = DeleteDocstrings().visit(stmt)
        ast.fix_missing_locations(stmt)
        self.out.extend(b"\n")
        self.out.extend(ast.unparse(stmt).encode())
        self.out.extend(b"\n")


class DeleteDocstrings(ast.NodeTransformer):
    """A visitor to delete docstrings from classes, functions and match cases."""

    def visit(self, node: Any) -> Any:
        """Visit the given AST node."""
        node = super().visit(node)
        match node:
            case ast.ClassDef() | ast.FunctionDef() | ast.match_case():
                match node.body:
                    case [ast.Expr(ast.Constant(str())), *rest]:
                        node.body = rest
                    case _:
                        pass
            case _:
                pass
        return node


class ReplaceVariables(ast.NodeTransformer):
    """A visitor to replace variables in an expression."""

    def __init__(self, vars: dict[str, ast.expr]) -> None:
        """Create a new ReplaceVariables transformer."""
        self.vars = vars

    def visit(self, node: Any) -> Any:
        """Visit the given AST node."""
        node = super().visit(node)
        match node:
            case ast.Name(name) if name in self.vars:
                return self.vars[name]
            case _:
                pass
        return node


if __name__ == "__main__":
    r = Compositor().dump()
    with open(COMPOSITE_PY, "wb") as f:
        f.write(r)
