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
from smt2._bitvector import rewrite as rewrite_bitvector
from smt2._constraint import Not, Symbol, Xor
from smt2._constraint import rewrite as rewrite_constraint

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
    term1 = Not(Not(Symbol(b"X")))
    term2 = Symbol(b"X")
    cmp = Xor(term1, term2)

    ctx = DumpContext()
    ctx.write(b"(assert ")
    cmp.dump(ctx)  # pyright: ignore[reportPrivateUsage]
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


def _parse_rewrite_bitvector() -> list[ast.match_case]:
    p = ast.parse(inspect.getsource(rewrite_bitvector))
    assert len(p.body) == 1 and isinstance(fn := p.body[0], ast.FunctionDef)
    assert len(fn.args.args) == 2
    assert len(fn.body) == 3
    # TODO: check assignments
    assert isinstance(m := fn.body[-1], ast.Match)
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
        term1 = _interpret_match(pattern, None)
        term2 = _interpret_rewrite(case.body, None)
        print(term1, term2)
        assert s.check(term1 != term2, *conds) == z3.unsat


@pytest.mark.parametrize("case", _parse_rewrite_bitvector())
def test_rewrite_bitvector(case: ast.match_case):
    for width in range(1, 65):  # TODO: expand range
        conds = list[z3.BoolRef]()
        match case.guard:
            case None:
                pass
            case ast.Compare(ast.Name(left), [ast.Eq()], [ast.Name(right)]):
                conds.append(z3.BitVec(left, width) == z3.BitVec(right, width))  # pyright: ignore[reportArgumentType]
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
            term1 = _interpret_match(pattern, width)
            term2 = _interpret_rewrite(case.body, width)
            print(term1, term2)
            # assert s.check(term1 != term2, *conds) == z3.unsat
            if s.check(term1 != term2, *conds) == z3.sat:
                print(s.model())
                assert False


def _interpret_match(
    pattern: ast.pattern, width: int | None
) -> z3.BoolRef | z3.BitVecRef:
    match pattern:
        case ast.MatchClass(ast.Name(name), patterns):
            return _interpret_z3(name, patterns, width, _interpret_match)
        case ast.MatchAs(None, str() as name):
            if name == "mask":
                assert width is not None
                return z3.BitVecVal((1 << width) - 1, width)
            elif name == "modulus":
                assert width is not None
                return z3.BitVecVal(1 << width, width)
            if width is None:
                return z3.Bool(name)
            else:
                return z3.BitVec(name, width)
        case ast.MatchSingleton(bool() as b):
            assert width is None
            res = z3.BoolVal(b)
        case ast.MatchSingleton(int() as i):
            assert width is not None
            res = z3.BitVecVal(i, width)
        case ast.MatchValue(value):
            return _interpret_expr(value, width)
        case ast.MatchClass(ast.Name(name)):
            raise TypeError(f"unhandled match class: {name}")
        case _:
            raise TypeError(f"unhandled pattern: {pattern.__class__}")
    assert not isinstance(res, z3.Probe)
    return res


def _interpret_rewrite(
    body: list[ast.stmt], width: int | None
) -> z3.BoolRef | z3.BitVecRef:
    for stmt in body:
        match stmt:
            case ast.Return(ast.expr() as value):
                return _interpret_expr(value, width)
            case _:
                raise NotImplementedError(stmt)
    raise SyntaxError("no return value")


def _interpret_expr(expr: ast.expr, width: int | None) -> z3.BoolRef | z3.BitVecRef:
    match expr:
        case ast.Call(ast.Name(name), args, []):
            return _interpret_z3(name, args, width, _interpret_expr)
        case ast.Call(ast.Subscript(ast.Name(name), _), args, []):
            # TODO: check width
            return _interpret_z3(name, args, width, _interpret_expr)
        case ast.UnaryOp(ast.Not(), operand):
            res = ~_interpret_expr(operand, width)
            assert not isinstance(res, z3.Probe)
            return res
        case ast.BinOp(left, ast.BitAnd(), right):
            res = _interpret_expr(left, width) & _interpret_expr(right, width)
            assert isinstance(res, z3.BoolRef) or isinstance(res, z3.BitVecRef)
            return res
        case ast.BinOp(left, ast.BitOr(), right):
            res = _interpret_expr(left, width) | _interpret_expr(right, width)
            assert isinstance(res, z3.BoolRef) or isinstance(res, z3.BitVecRef)
            return res
        case ast.BinOp(left, ast.BitXor(), right):
            return _interpret_expr(left, width) ^ _interpret_expr(right, width)
        case ast.BinOp(left, ast.Add(), right):
            res = _interpret_expr(left, width) + _interpret_expr(right, width)
            assert isinstance(res, z3.BitVecRef)
            return res
        case ast.BinOp(left, ast.Mod(), right):
            a, b = _interpret_expr(left, width), _interpret_expr(right, width)
            assert isinstance(a, z3.BitVecRef) and isinstance(b, z3.BitVecRef)
            return a % b
        case ast.Name(name):
            if name == "mask":
                assert width is not None
                return z3.BitVecVal((1 << width) - 1, width)
            elif name == "modulus":
                assert width is not None
                return z3.BitVecVal(1 << width, width)
            if width is None:
                return z3.Bool(name)
            else:
                return z3.BitVec(name, width)
        case ast.Constant(bool() as b):
            assert width is None
            return z3.BoolVal(b)
        case ast.Constant(int() as i):
            assert width is not None
            return z3.BitVecVal(i, width)
        case ast.BinOp(_, op, _):
            raise NotImplementedError(op)
        case _:
            raise NotImplementedError(expr)


def _interpret_z3[T: ast.pattern | ast.expr](
    name: str,
    args: list[T],
    width: int | None,
    fn: Callable[[T, int | None], z3.BoolRef | z3.BitVecRef],
) -> z3.BoolRef | z3.BitVecRef:
    match name, args:
        case "Value", [pattern]:
            res = fn(pattern, width)
        case "Value", [pattern, ast.MatchAs(None)]:
            res = fn(pattern, width)
        case "Value", [pattern, ast.Name("width")]:
            res = fn(pattern, width)
        case "Not", [pattern]:
            res = ~fn(pattern, width)
        case "And", [left, right]:
            res = fn(left, width) & fn(right, width)
        case "Or", [left, right]:
            res = fn(left, width) | fn(right, width)
        case "Xor", [left, right]:
            res = fn(left, width) ^ fn(right, width)
        case "Add", [left, right]:
            res = fn(left, width) + fn(right, width)  # TODO: which theory?
            assert isinstance(res, z3.BitVecRef)
        case _:
            raise TypeError(f"unknown operation: {name} ({len(args)} args)")
    assert not isinstance(res, z3.Probe)
    return res
