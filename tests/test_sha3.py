#!/usr/bin/env pytest

import pytest
from pysmt.shortcuts import Equals

from arrays import FrozenBytes
from sha3 import SHA3
from smt import Constraint, Uint256
from solver import Solver


def test_concrete() -> None:
    sha3 = SHA3()
    input = FrozenBytes.concrete(b"testing")
    assert (
        sha3[input].unwrap(bytes).hex()
        == "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    )


def test_symbolic() -> None:
    sha3 = SHA3()
    input = FrozenBytes.symbolic("INPUT", 7)
    assert sha3[input].maybe_unwrap() is None

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(
        Constraint(
            Equals(input._bigvector(), FrozenBytes.concrete(b"testing")._bigvector())
        )
    )
    assert solver.check()

    assert input.evaluate(solver) == b"testing".hex()
    sha3.narrow(solver)
    assert (
        solver.evaluate(sha3[input], True).unwrap(bytes).hex()
        == "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    )


def test_zero() -> None:
    sha3 = SHA3()
    assert (
        sha3[FrozenBytes.symbolic("INPUT", 0)].unwrap(bytes).hex()
        == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    )
    assert (
        sha3[FrozenBytes.concrete(b"")].unwrap(bytes).hex()
        == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    )


def test_impossible_concrete() -> None:
    sha3 = SHA3()
    input = FrozenBytes.symbolic("INPUT", 7)
    digest = sha3[input]

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(
        Constraint(
            Equals(input._bigvector(), FrozenBytes.concrete(b"testing")._bigvector())
        )
    )
    solver.assert_and_track(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert solver.check()

    # The initial `check()` succeeds, but an error is raised when we narrow the
    # SHA3 instance with the model.
    assert input.evaluate(solver) == b"testing".hex()
    with pytest.raises(AssertionError):
        sha3.narrow(solver)


def test_impossible_symbolic() -> None:
    sha3 = SHA3()
    digest = sha3[FrozenBytes.concrete(b"testing")]

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert not solver.check()


def test_items() -> None:
    sha3 = SHA3()
    sha3[FrozenBytes.concrete(b"hello")]
    sha3[FrozenBytes.concrete(b"testing")]

    items = sha3.items()
    n, k, _ = next(items)
    assert (n, k.maybe_unwrap()) == (5, b"hello")

    n, k, _ = next(items)
    assert (n, k.maybe_unwrap()) == (7, b"testing")

    with pytest.raises(StopIteration):
        next(items)


def test_printable() -> None:
    sha3 = SHA3()
    sha3[FrozenBytes.concrete(b"testing")]

    solver = Solver()
    sha3.constrain(solver)
    assert solver.check()
    sha3.narrow(solver)

    fixture = [
        "SHA3\t0x74657374696e67 -> 0x5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02",
        "",
    ]
    for actual, expected in zip(sha3.printable(solver), fixture, strict=True):
        assert actual == expected