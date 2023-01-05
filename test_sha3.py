#!/usr/bin/env pytest

import pytest
import z3

from sha3 import SHA3
from symbolic import BW, Solver, unwrap_bytes, zeval


def bytes_to_bitvector(data: bytes) -> z3.BitVecRef:
    return z3.BitVecVal(int.from_bytes(data), 8 * len(data))


def test_concrete() -> None:
    sha3 = SHA3()
    input = bytes_to_bitvector(b"testing")
    assert (
        unwrap_bytes(sha3[input]).hex()
        == "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    )


def test_symbolic() -> None:
    sha3 = SHA3()
    input = z3.BitVec("INPUT", 8 * 7)
    assert str(sha3[input]) == "SHA3(7)*[INPUT]"

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(input == bytes_to_bitvector(b"testing"), "TEST1")
    assert solver.check()

    model = solver.model()
    assert unwrap_bytes(zeval(model, input)) == b"testing"
    model = sha3.narrow(solver, model)
    assert (
        unwrap_bytes(zeval(model, sha3[input])).hex()
        == "5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02"
    )


def test_impossible_concrete() -> None:
    sha3 = SHA3()
    input = z3.BitVec("INPUT", 8 * 7)
    digest = sha3[input]
    assert str(digest) == "SHA3(7)*[INPUT]"

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(input == bytes_to_bitvector(b"testing"), "TEST1")
    solver.assert_and_track(
        digest
        == BW(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF),
        "TEST2",
    )
    assert solver.check()

    # The initial `check()` succeeds, but an error is raised when we narrow the
    # SHA3 instance with the model.
    model = solver.model()
    assert unwrap_bytes(zeval(model, input)) == b"testing"
    with pytest.raises(AssertionError):
        sha3.narrow(solver, model)


def test_impossible_symbolic() -> None:
    sha3 = SHA3()
    digest = sha3[bytes_to_bitvector(b"testing")]

    solver = Solver()
    sha3.constrain(solver)
    solver.assert_and_track(
        digest
        == BW(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF),
        "TEST1",
    )
    assert not solver.check()


def test_items() -> None:
    sha3 = SHA3()
    sha3[bytes_to_bitvector(b"hello")]
    sha3[bytes_to_bitvector(b"testing")]

    items = sha3.items()
    first, second = next(items), next(items)
    assert first[:2] == (5, bytes_to_bitvector(b"hello"))
    assert second[:2] == (7, bytes_to_bitvector(b"testing"))

    with pytest.raises(StopIteration):
        next(items)


def test_printable() -> None:
    sha3 = SHA3()
    sha3[bytes_to_bitvector(b"testing")]

    solver = Solver()
    sha3.constrain(solver)
    solver.check()
    model = solver.model()
    model = sha3.narrow(solver, model)

    fixture = [
        "SHA3\t0x74657374696e67 -> 0x5f16f4c7f149ac4f9510d9cf8cf384038ad348b3bcdc01915f95de12df9d1b02",
        "",
    ]
    for actual, expected in zip(sha3.printable(model), fixture, strict=True):
        assert actual == expected
