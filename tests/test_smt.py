#!/usr/bin/env pytest

import ast
import inspect
from typing import Callable

import pytest
import z3  # pyright: ignore[reportMissingTypeStubs]

from bytes import Bytes
from smt import (
    Array,
    Uint8,
    Uint256,
    concat_bytes,
    explode_bytes,
)
from smt2._base import DumpContext
from smt2._constraint import Not, Symbol, Xor, rewrite_constraint

# pyright: strict
# pyright: reportUnknownMemberType=none
# pyright: reportUnknownVariableType=none


def test_bvlshr_harder():
    assert (Uint256(0x1234) >> Uint256(1)).reveal() == 0x91A
    assert (Uint256(0x1234) >> Uint256(4)).reveal() == 0x123
    assert (Uint256(0x1234) >> Uint256(0)).reveal() == 0x1234
    assert (Uint256(0x1234) >> Uint256(257)).reveal() == 0

    a = Array[Uint256, Uint256]("BVLSHR0")
    b = Bytes(explode_bytes(a[Uint256(0)]))
    q = concat_bytes(
        Uint8(0x12),
        Uint8(0x34),
        Uint8(0x56),
        Uint8(0x78),
        *(b[Uint256(i)] for i in range(28)),
    )
    assert (q >> Uint256(0xE0)).reveal() == 0x12345678
    assert (q >> Uint256(0xE4)).reveal() == 0x1234567
    assert (q >> Uint256(0x123)).reveal() == 0


def test_simple_rewrite():
    term1 = Not(Not(Symbol("X")))
    term2 = Symbol("X")
    cmp = Xor(term1, term2)

    ctx = DumpContext()
    ctx.write(b"(assert ")
    cmp._dump(ctx)  # pyright: ignore[reportPrivateUsage]
    ctx.write(b")")
    smt = b"\n".join((*ctx.defs.values(), bytes(ctx.out))).decode()

    s = z3.Solver()
    s.add(z3.parse_smt2_string(smt))
    # print(smt)
    assert s.check() == z3.unsat


def _parse_rewrite_constraint() -> list[ast.match_case]:
    p = ast.parse(inspect.getsource(rewrite_constraint))
    assert len(p.body) == 1 and isinstance(fn := p.body[0], ast.FunctionDef)
    assert len(fn.args.args) == 1
    assert len(fn.body) == 1 and isinstance(m := fn.body[0], ast.Match)
    assert isinstance(m.subject, ast.Name) and m.subject.id == fn.args.args[0].arg
    return m.cases


@pytest.mark.parametrize("case", _parse_rewrite_constraint())
def test_rewrite_constraint(case: ast.match_case):
    conds = list[z3.BoolRef]()
    match case.guard:
        case None:
            pass
        case ast.Compare(ast.Name(left), [ast.Eq()], [ast.Name(right)]):
            conds.append(z3.Bool(left) == z3.Bool(right))  # pyright: ignore[reportArgumentType]
        case _:
            raise NotImplementedError(f"unknown guard: {case.guard}")
    match case.pattern:
        case ast.MatchAs(None, None):
            return  # terminal case
        case ast.MatchOr(patterns):
            pass
        case pattern:
            patterns = [pattern]
    s = z3.Solver()
    for pattern in patterns:
        term1 = _interpret_match(pattern)
        term2 = _interpret_rewrite(case.body)
        print(term1, term2)
        assert s.check(z3.Xor(term1, term2), *conds) == z3.unsat


def _interpret_match(pattern: ast.pattern) -> z3.BoolRef:
    match pattern:
        case ast.MatchClass(ast.Name(name), patterns):
            return _interpret_z3(name, patterns, _interpret_match)
        case ast.MatchAs(None, str() as name):
            return z3.Bool(name)
        case ast.MatchSingleton(bool() as b):
            res = z3.BoolVal(b)
        case ast.MatchClass(ast.Name(name)):
            raise TypeError(f"unhandled match class: {name}")
        case _:
            raise TypeError(f"unhandled pattern: {pattern.__class__}")
    assert isinstance(res, z3.BoolRef)
    return res


def _interpret_rewrite(body: list[ast.stmt]) -> z3.BoolRef:
    for stmt in body:
        match stmt:
            case ast.Return(ast.expr() as value):
                return _interpret_expr(value)
            case _:
                raise NotImplementedError(stmt)
    raise SyntaxError("no return value")


def _interpret_expr(expr: ast.expr) -> z3.BoolRef:
    match expr:
        case ast.Call(ast.Name(name), args, []):
            return _interpret_z3(name, args, _interpret_expr)
        case ast.UnaryOp(ast.Not(), operand):
            res = z3.Not(_interpret_expr(operand))
            assert isinstance(res, z3.BoolRef)
            return res
        case ast.Name(name):
            return z3.Bool(name)
        case ast.Constant(bool() as b):
            return z3.BoolVal(b)
        case _:
            raise NotImplementedError(expr)


def _interpret_z3[T: ast.pattern | ast.expr](
    name: str, args: list[T], fn: Callable[[T], z3.BoolRef]
) -> z3.BoolRef:
    match name, args:
        case "Value", [pattern]:
            res = fn(pattern)
        case "Not", [pattern]:
            res = z3.Not(fn(pattern))
        case "And", [left, right]:
            res = z3.And(fn(left), fn(right))
        case "Or", [left, right]:
            res = z3.Or(fn(left), fn(right))
        case "Xor", [left, right]:
            res = z3.Xor(fn(left), fn(right))
        case _:
            raise TypeError(f"unknown operation: {name} ({len(args)} args)")
    assert isinstance(res, z3.BoolRef)
    return res
