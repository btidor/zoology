"""
Code analysis of the rewrite library.

This analyzer uses an SMT solver to check that each rewrite case produces a
result that is equivalent to the matched input term.
"""
# ruff: noqa: F403, F405

from __future__ import annotations

import ast
import inspect
from dataclasses import dataclass
from itertools import product
from random import randint
from typing import Any, Callable, Iterable, Literal, Self

from . import theory_bitvec, theory_core
from .theory_bitvec import *
from .theory_core import *

# Run validation on all bitvector widths in the range [1, MAX_WIDTH] and all
# parameter values in the range [0, MAX_PARAM]. For now, these are set to low
# values for speed.
MAX_WIDTH = 8
MAX_PARAM = 2 * MAX_WIDTH

# Python ints must be represented as bitvectors also (because we want to perform
# boolean operations on them). Use a special, extra-large width for this to
# avoid overflow (must be able to multiply two MAX_WIDTH numbers without making
# the sign bit set).
NATIVE_WIDTH = 2 * MAX_WIDTH + 8
ZERO = BValue(0, NATIVE_WIDTH)

type Vars = tuple[tuple[str, FieldValue], ...]

type FieldValue = int | BaseTerm | tuple[BaseTerm, ...]

type FieldAnnotation = (
    Literal["CTerm"]
    | Literal["BTerm"]
    | Literal["S"]
    | Literal["int"]
    | Literal["bool"]
    | Literal["tuple[BTerm, ...]"]
)


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
                    assert " " not in id, f'invalid test case name: "{id}"'
                case _:
                    raise SyntaxError("every case should begin with a docstring")
            match case.pattern:
                case ast.MatchClass():
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
        self.guards = list[CTerm]()
        self.assertions = list[CTerm]()
        self.vars = dict[str, FieldValue]()

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
            # define the constructed input term as "term"
            vars = (*vars, ("term", term1))

            # create a new local scope, add bound variables
            parser = cls()
            for name, value in vars:
                assert name not in parser.vars, "duplicate definition"
                parser.vars[name] = value

            # 2. Handle any assignments in the prefix.
            for stmt in rw.prefix:
                match stmt:
                    case ast.Assign([ast.Name(name)], expr):
                        parser.vars[name] = parser.pyexpr(expr)
                    case _:
                        raise SyntaxError("expected assignment")

            # 3. Parse the guard, if present. (Relies on vars defined above.)
            if rw.guard:
                guard = parser.pyexpr(rw.guard)
                assert isinstance(guard, CTerm)
                parser.guards.append(guard)
                if not check(*parser.guards):
                    # if the guard is false, don't try to construct the body
                    continue

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
            goal = Eq(term1, term2)
            for a in parser.assertions:
                goal = And(goal, a)
            if check(*parser.guards, Not(goal)):
                return False
        return True

    @classmethod
    def match(
        cls, pattern: ast.pattern, sort: Sort | None
    ) -> Iterable[tuple[FieldValue, Vars]]:
        """Parse a match pattern of unknown type."""
        match pattern:
            case ast.MatchAs():
                yield from cls.match_as(pattern, sort)
            case ast.MatchClass():
                yield from cls.match_class(pattern)
            case ast.MatchStar():
                yield from cls.match_star(pattern)
            case _:
                raise SyntaxError(f"unsupported match pattern: {pattern}")

    @classmethod
    def match_as(
        cls, as_: ast.MatchAs, sort: Sort | None
    ) -> Iterable[tuple[FieldValue, Vars]]:
        """Parse a MatchAs pattern."""
        match (as_.pattern, as_.name):
            case (None, str() as name):
                # Capture pattern, e.g. "x" in `Neg(x)`. Generate a symbol and
                # add to locals.
                assert sort, "capture pattern requires sort"
                for sym in sort.symbol(name):
                    yield sym, ((name, sym),)
            case (None, None):
                # Wildcard pattern, i.e. `_`.
                assert sort, "wildcard pattern requires sort"
                for sym in sort.symbol():
                    yield sym, ()
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
                args = list[Iterable[tuple[FieldValue, Vars]]]()
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
                        case "tuple[BTerm, ...]":
                            assert isinstance(pat, ast.MatchSequence)
                            arg = list[tuple[FieldValue, Vars]]()
                            for prod in product(
                                *(cls.match(p, BitVectorSort) for p in pat.patterns)
                            ):
                                terms = list[BaseTerm]()
                                vars = list[tuple[str, FieldValue]]()
                                for t, v in prod:
                                    if isinstance(t, tuple):
                                        terms.extend(t)
                                    else:
                                        assert isinstance(t, BaseTerm)
                                        terms.append(t)
                                    vars.extend(v)
                                arg.append((tuple(terms), tuple(vars)))
                    args.append(arg)
                for parts in product(*args):
                    terms = list[FieldValue]()
                    vars = list[tuple[str, FieldValue]]()
                    for term, var in parts:
                        terms.append(term)
                        vars.extend(var)
                    try:
                        sym = op.cls(*terms)
                        if isinstance(sym, BTerm):
                            assert sym.width <= MAX_WIDTH
                        yield sym, tuple(vars)
                    except AssertionError:
                        # This combination of arguments is unconstructable (and
                        # so can never be matched). Skip!
                        pass

    @classmethod
    def match_param(cls, pattern: ast.pattern) -> Iterable[tuple[int, Vars]]:
        """Parse a match pattern where a param (raw Python int) is expected."""
        match pattern:
            case ast.MatchAs(None, str() as name):
                # AS pattern, e.g. "i" in `ZeroExtend(i, x)`.
                for i in range(0, MAX_PARAM + 1):
                    yield i, ((name, BValue(i, NATIVE_WIDTH)),)
            case ast.MatchValue(ast.Constant(int() as i)):
                # Literal pattern, e.g. "0" in `ZeroExtend(0, x)`.
                yield i, ()
            case _:
                raise SyntaxError(f"unsupported param pattern: {pattern}")

    @classmethod
    def match_star(
        cls, pattern: ast.MatchStar
    ) -> Iterable[tuple[tuple[BaseTerm, ...], Vars]]:
        """Parse a star pattern, used to capture variable-length Concat args."""
        assert pattern.name, "anonymous star not supported"
        for terms in variadic_sort(pattern.name):
            yield (terms, ((pattern.name, terms),))

    def pyexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a Python expression."""
        match expr:
            case ast.Name(name):
                term = self.vars[name]
                assert isinstance(term, BaseTerm)
                return term
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
                        if isinstance(left, BTerm) and left.width < NATIVE_WIDTH:
                            # When constructing the guard, return False if
                            # there's a width mismatch.
                            assert isinstance(right, BTerm)
                            assert right.width < NATIVE_WIDTH
                            if left.width != right.width:
                                return CValue(False)
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
            case ast.Attribute(ast.Name(name), "min"):
                val = self.vars[name]
                assert isinstance(val, BTerm)
                min = BSymbol(f"{name}.min".encode(), val.width)
                self.guards.append(Ule(min, val))
                return ZeroExtend(NATIVE_WIDTH - val.width, min)
            case ast.Attribute(ast.Name(name), "max"):
                val = self.vars[name]
                assert isinstance(val, BTerm)
                max = BSymbol(f"{name}.max".encode(), val.width)
                self.guards.append(Ule(val, max))
                return ZeroExtend(NATIVE_WIDTH - val.width, max)
            case ast.Attribute(ast.Name(name), attr):
                val = getattr(self.vars[name], attr)
                assert isinstance(val, int)
                return BValue(val, NATIVE_WIDTH)
            case ast.Call(ast.Name("len"), [ast.Name(name)]):
                tup = self.vars[name]
                assert isinstance(tup, tuple)
                return BValue(len(tup), NATIVE_WIDTH)
            case ast.Call(ast.Name("min"), [left, right]):
                left, right = self.pyexpr(left), self.pyexpr(right)
                assert isinstance(left, BTerm) and isinstance(right, BTerm)
                return Ite(Slt(left, right), left, right)
            case ast.Call(ast.Name("max"), [left, right]):
                left, right = self.pyexpr(left), self.pyexpr(right)
                assert isinstance(left, BTerm) and isinstance(right, BTerm)
                return Ite(Sgt(left, right), left, right)
            case _:
                raise SyntaxError(f"unsupported pyexpr: {expr}")

    def sexpr(self, expr: ast.expr) -> BaseTerm:
        """Recursively parse a symbolic expression."""
        match expr:
            case ast.Name(name):
                term = self.vars[name]
                assert isinstance(term, BaseTerm)
                return term
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
                res = list[FieldValue]()
                for a, f in zip(args, op.fields, strict=True):
                    if f == "int":
                        res.append(simplify(self.pyexpr(a)))
                    elif f == "tuple[BTerm, ...]":
                        r = list[BaseTerm]()
                        assert isinstance(a, ast.Tuple)
                        for el in a.elts:
                            match el:
                                case ast.Starred(ast.Name(rest)):
                                    term = self.vars[rest]
                                    assert isinstance(term, tuple)
                                    r.extend(term)
                                case _:
                                    r.append(self.sexpr(el))
                        res.append(tuple(r))
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
        case Smod(x, y):
            return (simplify(x) % simplify(y)) % (1 << term.width)
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


def variadic_sort(name: str, *prefix: BSymbol) -> Iterable[tuple[BSymbol, ...]]:
    """Create a tuple of Symbols for Concat, all combinations of widths."""
    yield prefix
    iname = f"{name}{len(prefix)}"
    pfxw = reduce(lambda p, q: p + q.width, prefix, 0)
    for width in range(1, MAX_WIDTH + 1 - pfxw):
        sym = BSymbol(iname.encode(), width)
        yield from variadic_sort(name, *prefix, sym)


class Op:
    """Represents an SMT operator, with metadata."""

    name: str
    cls: type[BaseTerm]
    fields: tuple[FieldAnnotation, ...]
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

        args = list[FieldAnnotation]()
        for name in self.cls.__match_args__:
            typ: str = self.cls.__dataclass_fields__[name].type
            if typ in ("CTerm", "BTerm", "S", "int", "bool", "tuple[BTerm, ...]"):
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
