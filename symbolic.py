"""Helpers for Z3 symbolic state."""

from __future__ import annotations

import contextlib
from typing import (
    Any,
    Iterator,
    Literal,
    Optional,
    TypeAlias,
    TypeGuard,
    TypeVar,
    Union,
    cast,
)

import z3
from Crypto.Hash import keccak

K = TypeVar("K")


Constraint: TypeAlias = Union[z3.ExprRef, Literal[True], Literal[False]]

uint8: TypeAlias = z3.BitVecRef
uint160: TypeAlias = z3.BitVecRef
uint256: TypeAlias = z3.BitVecRef


def BW(i: int) -> uint256:
    """Convert an integer word into a 256-bit bitvector."""
    if i >= (1 << 256) or i < 0:
        raise ValueError(f"invalid word: {i}")
    return z3.BitVecVal(i, 256)


def BA(i: int) -> uint160:
    """Convert an integer address into a 160-bit bitvector."""
    if i >= (1 << 160) or i < 0:
        raise ValueError(f"invalid address: {i}")
    return z3.BitVecVal(i, 160)


def BY(i: int) -> uint8:
    """Convert an integer byte into an 8-bit bitvector."""
    if i >= (1 << 8) or i < 0:
        raise ValueError(f"invalid byte: {i}")
    return z3.BitVecVal(i, 8)


def is_concrete(value: z3.BitVecRef) -> TypeGuard[z3.BitVecNumRef]:
    """Check whether a given bitvector is concrete or symbolic."""
    return cast(bool, z3.is_bv_value(simplify(value)))


def is_bitvector(value: Any) -> TypeGuard[z3.BitVecRef]:
    """Check whether a given variable is a bitvector."""
    return cast(bool, z3.is_bv(value))


def simplify(value: z3.BitVecRef) -> z3.BitVecRef:
    """Simplify a bitvector expression."""
    return cast(
        z3.BitVecRef,
        z3.simplify(
            value,
            blast_select_store=True,
            bv_extract_prop=True,
            bv_ineq_consistency_test_max=4,
            bv_ite2id=True,
            bv_le_extra=True,
            bv_not_simpl=True,
        ),
    )


def unwrap(value: z3.BitVecRef, msg: Optional[str] = None) -> int:
    """Unwrap a concrete bitvector expression into an int."""
    value = simplify(value)
    if not is_concrete(value):
        raise ValueError(msg or "unexpected symbolic value")
    return cast(int, value.as_long())


def unwrap_bytes(value: z3.BitVecRef, msg: Optional[str] = None) -> bytes:
    """Unwrap a concrete bitvector expression into bytes."""
    return unwrap(value, msg).to_bytes(value.size() // 8, "big")


def zeval(
    model: z3.ModelRef, value: z3.BitVecRef, model_completion: bool = False
) -> z3.BitVecRef:
    """Evaluate a given bitvector expression with the given model."""
    if not is_bitvector(value):
        raise ValueError("unexpected non-bitvector")
    return cast(z3.BitVecRef, model.eval(value, model_completion))


def zif(condition: Constraint, then: z3.BitVecRef, else_: z3.BitVecRef) -> z3.BitVecRef:
    """Return a symbolic if statement over bitvectors."""
    return cast(z3.BitVecRef, z3.If(condition, then, else_))


def zconcat(*values: z3.BitVecRef) -> z3.BitVecRef:
    """Return the concatenation of symbolic bitvectors."""
    # TODO: support zero-length bitvectors, empty hash, etc.
    return cast(z3.BitVecRef, z3.Concat(*values))


def zextract(high: int, low: int, value: z3.BitVecRef) -> z3.BitVecRef:
    """Return the result of slicing a symbolic bitvector."""
    return cast(z3.BitVecRef, z3.Extract(high, low, value))


def zand(*constraints: Constraint) -> z3.BoolRef:
    """Return the union of the given symbolic constraints."""
    return cast(z3.BoolRef, z3.And(*constraints))


def zor(*constraints: Constraint) -> z3.BoolRef:
    """Return the intersection of the given symbolic constraints."""
    return cast(z3.BoolRef, z3.Or(*constraints))


def zget(array: z3.ArrayRef, key: z3.BitVecRef) -> z3.BitVecRef:
    """Return the given element of the given array."""
    return cast(z3.BitVecRef, array[key])


def zstore(array: z3.ArrayRef, key: z3.BitVecRef, value: z3.BitVecRef) -> z3.ArrayRef:
    """Return the given element of the given array."""
    return cast(z3.ArrayRef, z3.Store(array, key, value))


def describe(value: z3.BitVecRef) -> str:
    """
    Produce a human-readable description of the given bitvector.

    For concrete bitvectors, returns a result in hexadecimal. Long values are
    broken into 256-bit chunks using dot syntax, e.g. "0x[1234.1]".

    For symbolic bitvectors, returns a hash based on the input variables.
    """
    value = simplify(value)
    if is_concrete(value):
        v: int = unwrap(value)
        if v < (1 << 256):
            return hex(v)
        p = []
        while v > 0:
            b = v & ((1 << 256) - 1)
            p.append(hex(b)[2:])
            v >>= 256
        return f"0x[{'.'.join(reversed(p))}]"
    else:
        digest = keccak.new(data=str(value).encode(), digest_bits=256).digest()
        return "#" + digest[:3].hex()


@contextlib.contextmanager
def solver_stack(solver: z3.Optimize) -> Iterator[None]:
    """Create a nested Z3 context using push()/pop()."""
    solver.push()
    try:
        yield
    finally:
        solver.pop()


def check(solver: z3.Optimize, *assumptions: Any) -> bool:
    """
    Check whether the given Z3 solver state is satisfiable.

    Returns true or false. Raises an error if Z3 fails.
    """
    check = solver.check(*assumptions)
    if check == z3.sat:
        return True
    elif check == z3.unsat:
        # Sometimes the solver return "unsat" but can't produce an unsatisfiable
        # core. Origintally I thought it was returning "unsat" incorrectly, but
        # that might not be true. This *can* happen if we add unnamed
        # constraints with `solver.add()` -- use `assert_and_track()` instead!
        assert len(solver.unsat_core()) > 0
        return False
    else:
        raise Exception(f"z3 failure: {solver.reason_unknown()}")
