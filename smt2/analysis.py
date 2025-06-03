"""Code analysis library for correctness checking."""

from __future__ import annotations

import ast
import inspect
from dataclasses import dataclass, fields
from random import randint
from typing import Any, Callable, Generator, NewType, Self, cast

from smt2 import theory_bitvec, theory_core

from .theory_bitvec import (
    Add,
    BAnd,
    BitVector,
    BOr,
    BSymbol,
    BValue,
    BXor,
    Extract,
    Lshr,
    Mul,
    Sdiv,
    Sge,
    Sgt,
    Shl,
    Sle,
    Slt,
    Smod,
    Sub,
    Ult,
    ZeroExtend,
)
from .theory_core import (
    And,
    Base,
    Constraint,
    CSymbol,
    CValue,
    Distinct,
    Eq,
    Not,
    Or,
    check,
)

# During analysis, all values are symbolic (type Constraint, etc.). This
# includes values that are symbolic at runtime (e.g. Not(...)) and those that
# are instances of concrete Python types (e.g. True). We want to be explicit
# about which context we're operating in, and these type wrappers force us to
# convert between the two explicitly.
PythonType = NewType("PythonType", Base)
SymbolicType = NewType("SymbolicType", Base)

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

    def __init__(self, pre: Casette, width: int | None) -> None:
        """Create a new CaseParser."""
        self.case = pre.case
        self.prefix = pre.prefix
        self.assertions = list[Constraint]()
        self.pyvars = dict[str, PythonType]()
        self.svars = dict[str, SymbolicType]()
        self.sort = ConstraintSort() if width is None else BitVectorSort(width)

    def is_equivalent(self) -> bool:
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
        term1 = self._match(self.case.pattern, self.sort)
        self.svars["term"] = term1

        # 1.5. Handle any assignments in the prefix.
        for stmt in self.prefix:
            match stmt:
                case ast.Expr(ast.Constant(str())):
                    pass  # function docstring, just ignore
                case ast.Assign([ast.Name(name)], expr):
                    self.pyvars[name] = self._pyexpr(expr)
                case _:
                    raise SyntaxError("expected assignment")

        # 2. Parse the guard, if present. (Relies on vars defined in #1).
        match self.case.guard:
            case None:
                guard = CValue(True)
            case ast.Compare(ast.Name(name), [ast.Eq()], [right]) if name in self.svars:
                # Comparing symbolic types (special!). If two ASTs are equal,
                # the expressions must be equal.
                #
                # Note: the opposite is not true, and this substitution may not
                # be safe in other contexts.
                #
                # Note: it's unsafe to implement != because if two ASTs are
                # distinct, that tells us nothing about whether or not the
                # expressions are equal.
                guard = Eq(self.svars[name], self._sexpr(right))
            case normal:
                # Assume we're comparing Python types, proceed as usual.
                expr = self._pyexpr(normal)
                assert isinstance(expr, Constraint)
                guard = expr

        # 3. Parse the body. This tells us the value of the rewritten term.s
        for stmt in self.case.body:
            match stmt:
                case ast.Expr(ast.Constant(str())):
                    pass  # skip docstring
                case ast.Assign([ast.Name(name)], expr):
                    self.pyvars[name] = self._pyexpr(expr)
                case ast.Return(ast.expr() as expr):
                    term2 = self._sexpr(expr)
                    break
                case _:
                    raise NotImplementedError("unknown statement", stmt)
        else:
            raise SyntaxError("expected trailing return")

        # 4. Check!
        goal = Eq(term1, term2)
        for a in self.assertions:
            goal = And(goal, a)
        return not check(Not(goal), guard)

    def _match(self, pattern: ast.pattern, sort: Sort) -> SymbolicType:
        """Recursively parse a case statement pattern."""
        match pattern:
            case ast.MatchAs(None, None):
                # Underscore name, e.g. `Ite(_, x, y)`. Generate random label.
                return SymbolicType(sort.symbol(f"_{randint(0, 2**16)}"))
            case (
                ast.MatchAs(None, str() as name)
                | ast.MatchAs(ast.MatchClass(ast.Name("Constraint"), []), str() as name)
                | ast.MatchAs(ast.MatchClass(ast.Name("BitVector"), []), str() as name)
            ):
                # Proper name, e.g. `Neg(x)` (possibly qualified with a simple
                # type). Generate symbol and add to locals.
                self.svars[name] = SymbolicType(sort.symbol(name))
                return self.svars[name]
            case ast.MatchAs(cls, str() as name) if cls:
                # Named sub-expression, e.g. `Value(a) as x`. Process as usual,
                # then add to locals.
                self.svars[name] = self._match(cls, sort)
                return self.svars[name]
            case ast.MatchClass(ast.Name(name), patterns):
                # Simple class, e.g. `Not(...)`. Assumed to be from the same
                # theory as the test case.
                return self._match_symbolic(name, patterns, self.sort)
            case _:
                raise NotImplementedError("unsupported pattern", pattern)

    def _match_symbolic(
        self, name: str, patterns: list[ast.pattern], sort: Sort
    ) -> SymbolicType:
        """Parse a symbolic term from a match statement."""
        match name, patterns:
            case "Symbol", _:
                raise SyntaxError("Symbol is not supported")
            case "CValue", [ast.MatchSingleton(bool() as b)]:
                return SymbolicType(ConstraintSort().value(b))
            case "BValue", [ast.MatchValue(ast.Constant(int() as i))]:
                assert isinstance(sort, BitVectorSort)
                return SymbolicType(sort.value(i))
            case "CValue" | "BValue" as kind, [ast.MatchAs(_, str() as name)]:
                # Named value, e.g. `Value(foo)`. Note that `foo` is defined as
                # a Python type, while `Value(foo)` is a symbolic type. We know
                # that `foo` fits in the given width, though.
                assert name not in self.svars, "duplicate name"
                match kind:
                    case "CValue":
                        self.pyvars[name] = PythonType(ConstraintSort().symbol(name))
                        return SymbolicType(self.pyvars[name])
                    case "BValue":
                        assert isinstance(sort, BitVectorSort)
                        sym = sort.symbol(name)
                        self.pyvars[name] = PythonType(
                            ZeroExtend(MAX_WIDTH - sort.width, sym)
                        )
                        return SymbolicType(sym)
            case "CValue" | "BValue", [pattern]:
                raise TypeError("unexpected match on Value(...)", pattern)
            case "CValue" | "BValue", _:
                raise TypeError("may only match on single-argument `Value(...)`")
            case _, _:
                # Class from theory, e.g. `Not(...)`. Parse the field
                # annotations to determine the type of the inner expressions.
                cls = operator(name)
                args = list[SymbolicType]()
                filtered = filter(lambda f: f.init and not f.kw_only, fields(cls))
                for field, pattern in zip(filtered, patterns, strict=True):
                    if field.type == "Constraint":
                        arg = self._match(pattern, ConstraintSort())
                    elif field.type == "BitVector[N]" or field.type == "BitVector":
                        assert isinstance(sort, BitVectorSort)
                        arg = self._match(pattern, sort)
                    elif field.type == "S":
                        # When matching a generic field, check if an explicit
                        # class was given in the case pattern.
                        match pattern:
                            case ast.MatchAs(ast.MatchClass(ast.Name("Constraint"))):
                                arg = self._match(pattern, ConstraintSort())
                            case ast.MatchAs(ast.MatchClass(ast.Name("BitVector"))):
                                assert isinstance(self.sort, BitVectorSort)
                                arg = self._match(pattern, self.sort)
                            case _:
                                arg = self._match(pattern, sort)
                    elif field.type == "int":
                        match pattern:
                            case ast.MatchValue(ast.Constant(k)):
                                arg = k
                            case _:
                                raise NotImplementedError("unknown constant", pattern)
                    else:
                        raise NotImplementedError("unknown field type", field.type)
                    args.append(arg)
                return cls(*args)

    def _pyexpr(self, expr: ast.expr) -> PythonType:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                return self.pyvars[name]
            case ast.Constant(bool() as b):
                return PythonType(CValue(b))
            case ast.Constant(int() as i):
                return PythonType(BValue(i, MAX_WIDTH))
            case ast.UnaryOp(op, operand):
                operand = self._pyexpr(operand)
                match op:
                    case ast.Not():
                        assert isinstance(operand, Constraint)
                        return PythonType(Not(operand))
                    case _:
                        raise NotImplementedError(op)
            case ast.BinOp(left, op, right):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, BitVector) and isinstance(right, BitVector)
                rnonzero = Distinct(right, ZERO)
                nonneg = And(Sge(left, ZERO), Sge(right, ZERO))
                match op:
                    case ast.Add():
                        return PythonType(Add(left, right))
                    case ast.Sub():
                        return PythonType(Sub(left, right))
                    case ast.Mult():
                        return PythonType(Mul(left, right))
                    case ast.FloorDiv():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return PythonType(Sdiv(left, right))
                    case ast.Mod():
                        self.assertions.append(rnonzero)  # else ZeroDivisionError
                        return PythonType(Smod(left, right))
                    case ast.BitAnd():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(BAnd(left, right))
                    case ast.BitOr():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(BOr(left, right))
                    case ast.BitXor():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(BXor(left, right))
                    case ast.LShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(Shl(left, right))
                    case ast.RShift():
                        self.assertions.append(nonneg)  # else incorrect result
                        return PythonType(Lshr(left, right))
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
                        return PythonType(Slt(left, right))
                    case ast.LtE():
                        return PythonType(Sle(left, right))
                    case ast.Gt():
                        return PythonType(Sgt(left, right))
                    case ast.GtE():
                        return PythonType(Sge(left, right))
                    case _:
                        raise NotImplementedError(op)
            case ast.BoolOp(op, [left, right]):
                left, right = self._pyexpr(left), self._pyexpr(right)
                assert isinstance(left, Constraint) and isinstance(right, Constraint)
                match op:
                    case ast.And():
                        return PythonType(And(left, right))
                    case ast.Or():
                        return PythonType(Or(left, right))
                    case _:
                        raise NotImplementedError(op)
            case ast.Attribute(ast.Name(name), attr):
                val = getattr(self.svars[name], attr)
                assert isinstance(val, int)
                return PythonType(BValue(val, MAX_WIDTH))
            case _:
                raise NotImplementedError(expr)

    def _sexpr(self, expr: ast.expr) -> SymbolicType:
        """Recursively parse a symbolic expression."""
        match expr:
            case ast.Name(name):
                return self.svars[name]
            case ast.Call(ast.Name("cast"), [_, arg]):
                return self._sexpr(arg)  # ignore casts
            case ast.Call(ast.Name("Symbol")):
                raise SyntaxError("Symbol is not supported")
            case ast.Call(ast.Name("CValue"), [arg]):
                return SymbolicType(self._pyexpr(arg))
            case ast.Call(ast.Name("BValue"), [arg, width]):
                inner = self._pyexpr(arg)
                assert isinstance(inner, BitVector)
                match cast(Base, self._pyexpr(width)):
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
                return SymbolicType(Extract(width - 1, 0, inner))
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

    def symbol(self, name: str) -> Constraint:
        """Create a Symbol with the given name."""
        return CSymbol(name.encode())

    def value(self, val: bool) -> Constraint:
        """Create a concrete Value."""
        return CValue(val)


@dataclass(frozen=True, slots=True)
class BitVectorSort[N: int]:
    """Represents a BitVector sort."""

    width: N

    def symbol(self, name: str) -> BitVector:
        """Create a Symbol with the given name."""
        return BSymbol(name.encode(), self.width)

    def value(self, val: int) -> BitVector:
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
