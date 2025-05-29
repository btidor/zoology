"""Code analysis library for correctness checking."""

from __future__ import annotations

import ast
import copy
import inspect
from dataclasses import dataclass, fields
from random import randint
from typing import Any, Callable, Generator, NewType, Self

from . import bv, core
from .bv import BitVector
from .core import Constraint, Distinct, Eq, Symbolic, check

# During analysis, all values are symbolic (type Constraint, etc.). This
# includes values that are symbolic at runtime (e.g. Not(...)) and those that
# are instances of concrete Python types (e.g. True). We want to be explicit
# about which context we're operating in, and these type wrappers force us to
# convert between the two explicitly.
PythonType = NewType("PythonType", Symbolic)
SymbolicType = NewType("SymbolicType", Symbolic)

# When handling Python ints, assume they fit in a fixed (large) number of bytes.
MAX_WIDTH = 128
ZERO = bv.Value(0, MAX_WIDTH)


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
        self.case = pre.case
        self.assertions = list[Constraint]()
        self.term1, self.guard, self.term2 = None, None, None
        self.pyvars = dict[str, PythonType]()
        self.svars = dict[str, SymbolicType]()
        self.sort = ConstraintSort() if width is None else BitVectorSort(width)

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

    def parse_pattern(self) -> Generator[Self]:
        """
        Step One: parse the case's pattern.

        Example: `case Not(Value(v)): ...`:
        * define a new bool/int named "v"
        * return the input (original) term: Not(Symbol("v"))

        Yields a new CaseParser, or in the case of an "or" pattern, multiple
        CaseParsers.
        """
        assert not self.term1 and not self.guard and not self.term2, "out of order"
        match self.case.pattern:
            case ast.MatchOr(patterns):
                for pattern in patterns:
                    ctx = copy.deepcopy(self)
                    ctx.term1 = ctx._match(pattern, self.sort)  # may define new vars
                    yield ctx
            case pattern:
                self.term1 = self._match(pattern, self.sort)  # may define new vars
                yield self

    def parse_guard(self) -> None:
        """
        Step Two: parse the case's guard, if present.

        Example: `case <pattern> if <guard>: <body>`.

        This must occur after parse_pattern() because the guard expression
        typically uses variables defined in the pattern.
        """
        assert self.term1 and not self.guard and not self.term2, "out of order"
        match self.case.guard:
            case None:
                self.guard = core.Value(True)
            case ast.Compare(ast.Name(name), [ast.Eq()], [right]) if name in self.svars:
                # Comparing symbolic types (special!). If two ASTs are
                # equal, the expressions must be equal.
                #
                # Note: the opposite is not true, and this substitution may
                # not be safe in other contexts.
                #
                # Note: it's unsafe to implement != because if two ASTs are
                # distinct, that tells us nothing about whether or not the
                # expressions are equal.
                #
                self.guard = Eq(self.svars[name], self._sexpr(right))
            case normal:
                # Assume we're comparing Python types, proceed as usual.
                expr = self._pyexpr(normal)
                assert isinstance(expr, Constraint)
                self.guard = expr

    def parse_body(self) -> None:
        """
        Step Three: parse the case's body.

        Returns a symbolic term representing the value returned from the body,
        i.e. the rewritten term.
        """
        assert self.term1 and self.guard and not self.term2, "out of order"
        match self.case.body[-1]:
            case ast.Return(ast.expr() as expr):
                self.term2 = self._sexpr(expr)
            case _:
                raise SyntaxError("expected trailing return")

    def equivalent(self) -> bool:
        """Step Four: check equivalence."""
        assert self.term1 and self.guard and self.term2, "out of order"
        goal = Eq(self.term1, self.term2)
        for a in self.assertions:
            goal = core.And(goal, a)
        return not check(core.Not(goal), self.guard)

    def _match(self, pattern: ast.pattern, sort: Sort) -> SymbolicType:
        """Recursively parse a case statement pattern."""
        match pattern:
            case ast.MatchAs(_, None):
                # Underscore name. Generate random label.
                return SymbolicType(sort.symbol(f"_{randint(0, 2**16)}"))
            case ast.MatchAs(_, str() as name):
                # Proper name. Generate symbol and add to locals.
                assert name not in self.pyvars, "duplicate name"
                self.svars[name] = SymbolicType(sort.symbol(name))
                return self.svars[name]
            case ast.MatchClass(ast.Name(name), patterns):
                # Simple class, e.g. `Not(...)`. Assumed to be from the same
                # theory as the test case.
                return self._match_symbolic(name, patterns, self.sort)
            case ast.MatchClass(ast.Attribute(ast.Name("core"), name), patterns):
                # Qualified class, e.g. `core.Not(...)`. Used in BitVector
                # rewrites to access logic from the core theory.
                return self._match_symbolic(name, patterns, ConstraintSort())
            case _:
                raise NotImplementedError("unsupported pattern", pattern)

    def _match_symbolic(
        self, name: str, patterns: list[ast.pattern], sort: Sort
    ) -> SymbolicType:
        """Parse a symbolic term from a match statement."""
        match name, patterns:
            case "Symbol", _:
                raise SyntaxError("Symbol is not supported")
            case "Value", [ast.MatchSingleton(bool() as b)]:
                # Constant value, e.g. `core.Value(True)`.
                assert isinstance(sort, ConstraintSort)
                return SymbolicType(sort.value(b))
            case "Value", [ast.MatchValue(ast.Constant(int() as i))]:
                # Constant value, e.g. `bv.Value(1)`.
                assert isinstance(sort, BitVectorSort)
                return SymbolicType(sort.value(i))
            case "Value", [ast.MatchAs(_, str() as name)]:
                # Named value, e.g. `Value(foo)`. Note that `foo` is defined as
                # a Python type, while `Value(foo)` is a symbolic type. We know
                # that `foo` fits in the given width, though.
                assert name not in self.svars, "duplicate name"
                match sort:
                    case ConstraintSort():
                        self.pyvars[name] = PythonType(sort.symbol(name))
                        return SymbolicType(self.pyvars[name])
                    case BitVectorSort(width):
                        sym = sort.symbol(name)
                        self.pyvars[name] = PythonType(
                            bv.ZeroExtend[int](MAX_WIDTH - width, sym)
                        )
                        return SymbolicType(sym)
            case "Value", [pattern]:
                raise TypeError("unexpected match on Value(...)", pattern)
            case "Value", _:
                raise TypeError("may only match on single-argument `Value(...)`")
            case _, _:
                # Class from theory, e.g. `Not(...)`. Parse the field
                # annotations to determine the type of the inner expressions.
                cls = sort.operator(name)
                args = list[SymbolicType]()
                for field, pattern in zip(fields(cls), patterns, strict=True):
                    if field.type == "Constraint":
                        subsort = ConstraintSort()
                    elif field.type == "BitVector[N]":
                        assert isinstance(sort, BitVectorSort)
                        subsort = sort
                    elif field.type == "S":
                        # When matching a generic field, check if an explicit
                        # class was given in the case pattern.
                        match pattern:
                            case ast.MatchAs(ast.MatchClass(ast.Name("Constraint"))):
                                subsort = ConstraintSort()
                            case ast.MatchAs(ast.MatchClass(ast.Name("BitVector"))):
                                assert isinstance(self.sort, BitVectorSort)
                                subsort = self.sort
                            case _:
                                subsort = sort
                    else:
                        raise NotImplementedError("unknown field type", field.type)
                    args.append(self._match(pattern, subsort))
                return cls(*args)

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
                assert isinstance(left, BitVector) and isinstance(right, BitVector)
                rnonzero = Distinct(right, ZERO)
                nonneg = core.And(bv.Sge(left, ZERO), bv.Sge(right, ZERO))
                match op:
                    case ast.Add():
                        return PythonType(bv.Add[int](left, right))
                    case ast.Sub():
                        return PythonType(bv.Sub[int](left, right))
                    case ast.Mult():
                        return PythonType(bv.Mul[int](left, right))
                    case ast.FloorDiv():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return PythonType(bv.Sdiv[int](left, right))
                    case ast.Mod():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return PythonType(bv.Smod[int](left, right))
                    case ast.BitAnd():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(bv.And[int](left, right))
                    case ast.BitOr():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(bv.Or[int](left, right))
                    case ast.BitXor():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(bv.Xor[int](left, right))
                    case ast.LShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(bv.Shl[int](left, right))
                    case ast.RShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(bv.Lshr[int](left, right))
                    case _:
                        raise NotImplementedError(op)
            case ast.Compare(left, [op], [right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, BitVector) and isinstance(right, BitVector)
                match op:
                    case ast.Eq():
                        return PythonType(Eq(left, right))
                    case ast.NotEq():
                        return PythonType(Distinct(left, right))
                    case ast.Lt():
                        return PythonType(bv.Slt[int](left, right))
                    case ast.LtE():
                        return PythonType(bv.Sle[int](left, right))
                    case ast.Gt():
                        return PythonType(bv.Sgt[int](left, right))
                    case ast.GtE():
                        return PythonType(bv.Sge[int](left, right))
                    case _:
                        raise NotImplementedError(op)
            case ast.BoolOp(op, [left, right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, Constraint) and isinstance(right, Constraint)
                match op:
                    case ast.And():
                        return PythonType(core.And(left, right))
                    case ast.Or():
                        return PythonType(core.Or(left, right))
                    case _:
                        raise NotImplementedError(op)
            case _:
                raise NotImplementedError(expr)

    def _sexpr(self, expr: ast.expr) -> SymbolicType:
        """Recursively parse a symbolic expression."""
        match expr, self.sort:
            case ast.Name(name), _:
                return self.svars[name]
            case ast.Call(ast.Name("Symbol")), _:
                raise SyntaxError("Symbol is not supported")
            case (ast.Call(ast.Name("Value"), args), ConstraintSort()) | (
                ast.Call(ast.Attribute(ast.Name("core"), "Value"), args),
                _,
            ):
                assert len(args) == 1
                return SymbolicType(self._pyexpr(args[0]))
            case ast.Call(ast.Name("Value"), args), BitVectorSort():
                assert len(args) == 2
                # No width-changing operations for now...
                assert isinstance(args[1], ast.Name) and args[1].id == "width"
                inner = self._pyexpr(args[0])
                assert isinstance(inner, BitVector)
                # Note that Value(...) converts an inner Python type to an outer
                # symbolic type. We assert that the conversion does not
                # overflow.
                self.assertions.append(
                    bv.Ult(inner, bv.Value(1 << self.sort.width, MAX_WIDTH))
                )
                return SymbolicType(bv.Extract[int](self.sort.width - 1, 0, inner))
            case ast.Call(func, args), _:  # Not(...), etc.
                if isinstance(func, ast.Subscript):
                    func = func.value  # ignore type annotations, e.g. Ult[int]
                match func:
                    case ast.Name(name):
                        cls = self.sort.operator(name)
                    case ast.Attribute(ast.Name("core"), name):
                        cls = ConstraintSort().operator(name)
                    case _:
                        raise NotImplementedError(func)
                return cls(*(self._sexpr(a) for a in args))
            case _:
                raise NotImplementedError(expr)


type Sort = ConstraintSort | BitVectorSort[int]


@dataclass(frozen=True, slots=True)
class ConstraintSort:
    """Represents the boolean sort."""

    def symbol(self, name: str) -> Constraint:
        """Create a Symbol with the given name."""
        return core.Symbol(name.encode())

    def value(self, val: bool) -> Constraint:
        """Create a concrete Value."""
        return core.Value(val)

    def operator(self, name: str) -> Any:
        """Return the given operator from the theory."""
        return core.__dict__[name]


@dataclass(frozen=True, slots=True)
class BitVectorSort[N: int]:
    """Represents a BitVector sort."""

    width: N

    def symbol(self, name: str) -> BitVector[N]:
        """Create a Symbol with the given name."""
        return bv.Symbol(name.encode(), self.width)

    def value(self, val: int) -> BitVector[N]:
        """Create a concrete Value."""
        assert 0 <= val < (1 << self.width)
        return bv.Value(val, self.width)

    def operator(self, name: str) -> Any:
        """Return the given operator from the theory."""
        return bv.__dict__[name]
