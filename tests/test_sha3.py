#!/usr/bin/env pytest

import pytest

from bytes import BYTES, Bytes
from sha3 import SHA3
from smt import NarrowingError, Solver, Uint256


def test_concrete() -> None:
    sha3 = SHA3()
    input = Bytes(b"testing")
    digest, _ = sha3.hash(input)
    assert (
        digest.reveal()
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_symbolic() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT", 7)
    digest, constraint = sha3.hash(input)
    assert digest.reveal() is None

    solver = Solver()
    solver.add(constraint)
    solver.add(input.bigvector() == Bytes(b"testing").bigvector())
    assert solver.check()

    assert input.evaluate(solver) == b"testing"
    sha3.narrow(solver)
    digest, constraint = sha3.hash(input)
    assert (
        solver.evaluate(digest)
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_fully_symbolic() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT")
    digest, constraint = sha3.hash(input)
    assert digest.reveal() is None

    solver = Solver()
    solver.add(constraint)
    solver.add(input.length == Uint256(7))
    for i, b in enumerate(b"testing"):
        solver.add(input[Uint256(i)] == BYTES[b])

    digest, constraint = sha3.hash(input)
    solver.add(constraint)
    assert solver.check()

    assert input.evaluate(solver) == b"testing"
    sha3.narrow(solver)
    assert (
        solver.evaluate(digest)
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_zero() -> None:
    sha3 = SHA3()
    digest, _ = sha3.hash(Bytes.symbolic("INPUT", 0))
    assert (
        digest.reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )
    digest, _ = sha3.hash(Bytes())
    assert (
        digest.reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )


def test_impossible_concrete() -> None:
    sha3 = SHA3()
    input = Bytes.symbolic("INPUT", 7)
    digest, constraint = sha3.hash(input)

    solver = Solver()
    solver.add(constraint)
    solver.add(input.bigvector() == Bytes(b"testing").bigvector())
    solver.add(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert solver.check()

    # The initial `check()` succeeds, but an error is raised when we narrow the
    # SHA3 instance with the model.
    assert input.evaluate(solver) == b"testing"
    with pytest.raises(NarrowingError):
        sha3.narrow(solver)


def test_impossible_symbolic() -> None:
    sha3 = SHA3()
    digest, constraint = sha3.hash(Bytes(b"testing"))

    solver = Solver()
    solver.add(constraint)
    solver.add(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert not solver.check()
