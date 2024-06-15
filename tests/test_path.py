#!/usr/bin/env pytest

import pytest

from bytes import BYTES, Bytes
from path import Path
from smt import NarrowingError, Solver, Uint256


def test_concrete() -> None:
    path = Path()
    input = Bytes(b"testing")
    digest = path.keccak256(input)
    assert (
        digest.reveal()
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_symbolic() -> None:
    path = Path()
    input = Bytes.symbolic("INPUT", 7)
    digest = path.keccak256(input)
    assert digest.reveal() is None

    solver = Solver()
    solver.add(path.constraint)
    solver.add(input.bigvector() == Bytes(b"testing").bigvector())
    assert solver.check()

    assert input.evaluate(solver) == b"testing"
    path.narrow(solver)
    assert (
        solver.evaluate(digest)
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_fully_symbolic() -> None:
    path = Path()
    input = Bytes.symbolic("INPUT")
    digest = path.keccak256(input)
    assert digest.reveal() is None

    solver = Solver()
    solver.add(input.length == Uint256(7))
    for i, b in enumerate(b"testing"):
        solver.add(input[Uint256(i)] == BYTES[b])

    digest = path.keccak256(input)
    solver.add(path.constraint)
    assert solver.check()

    assert input.evaluate(solver) == b"testing"
    path.narrow(solver)
    assert (
        solver.evaluate(digest)
        == 0x5F16F4C7F149AC4F9510D9CF8CF384038AD348B3BCDC01915F95DE12DF9D1B02
    )


def test_zero() -> None:
    path = Path()
    digest = path.keccak256(Bytes.symbolic("INPUT", 0))
    assert (
        digest.reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )
    digest = path.keccak256(Bytes())
    assert (
        digest.reveal()
        == 0xC5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470
    )


def test_impossible_concrete() -> None:
    path = Path()
    input = Bytes.symbolic("INPUT", 7)
    digest = path.keccak256(input)

    solver = Solver()
    solver.add(path.constraint)
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
        path.narrow(solver)


def test_impossible_symbolic() -> None:
    path = Path()
    digest = path.keccak256(Bytes(b"testing"))

    solver = Solver()
    solver.add(path.constraint)
    solver.add(
        digest
        == Uint256(0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF)
    )
    assert not solver.check()
