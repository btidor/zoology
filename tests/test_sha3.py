#!/usr/bin/env pytest

import pytest

from bytes import Bytes
from sha3 import SHA3
from smt import NarrowingError, Solver, Uint256


def test_concrete() -> None:
    sha3 = SHA3()
    input = Bytes(b"testing")
    assert (
        sha3[input].reveal()
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_symbolic() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT", 7)
    assert sha3[input].reveal() is None

    solver = Solver()
    sha3.constrain(solver)
    solver.add(input.bigvector(7) == Bytes(b"testing").bigvector(7))
    assert solver.check()

    assert input.describe(solver) == b"testing".hex()
    sha3.narrow(solver)
    assert (
        solver.evaluate(sha3[input])
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_fully_symbolic() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT")
    assert sha3[input].reveal() is None

    solver = Solver()
    sha3.constrain(solver)
    solver.add(input.bigvector(7) == Bytes(b"testing").bigvector(7))
    solver.add(input.length == Uint256(7))
    assert solver.check()

    assert input.describe(solver) == b"testing".hex()
    sha3.narrow(solver)
    assert (
        solver.evaluate(sha3[input])
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_zero() -> None:
    sha3 = SHA3()
    assert (
        sha3[Bytes.symbolic("INPUT", 0)].reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )
    assert (
        sha3[Bytes()].reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )


def test_impossible_concrete() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT", 7)
    digest = sha3[input]

    solver = Solver()
    sha3.constrain(solver)
    solver.add(input.bigvector(7) == Bytes(b"testing").bigvector(7))
    solver.add(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert solver.check()

    # The initial `check()` succeeds, but an error is raised when we narrow the
    # SHA3 instance with the model.
    assert input.describe(solver) == b"testing".hex()
    with pytest.raises(NarrowingError):
        sha3.narrow(solver)


def test_impossible_symbolic() -> None:
    sha3 = SHA3()
    digest = sha3[Bytes(b"testing")]

    solver = Solver()
    sha3.constrain(solver)
    solver.add(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert not solver.check()


def test_items() -> None:
    sha3 = SHA3()
    sha3[Bytes(b"hello")]
    sha3[Bytes(b"testing")]

    items = sha3.items()
    n, k, _ = next(items)
    assert (n, k.reveal()) == (5, int.from_bytes(b"hello"))

    n, k, _ = next(items)
    assert (n, k.reveal()) == (7, int.from_bytes(b"testing"))

    with pytest.raises(StopIteration):
        next(items)


def test_printable() -> None:
    sha3 = SHA3()
    sha3[Bytes(b"testing")]

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
