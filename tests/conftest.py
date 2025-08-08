# ruff: noqa: E402

# Provide smart debug info for assertions that appear in these non-test modules.
# Must appear *before* the module is imported. See:
# https://docs.pytest.org/en/latest/how-to/assert.html#assert-introspection


import pytest

import smt

pytest.register_assert_rewrite("helpers", "solidity")


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption("--profile", dest="profile", action="store_true")
    parser.addoption("--memory", dest="memory", action="store_true")


### ### ### ### ###

import gc
from typing import Any, Iterator

from smt2 import theory_core
from smt2.composite import CacheMeta
from smt2.theory_core import CACHE, BaseTerm, make_bitwuzla


@pytest.fixture(autouse=True)
def reset_bitwuzla(request: Any) -> Iterator[None]:
    theory_core.BZLA = make_bitwuzla()
    CACHE.clear()
    CacheMeta._cache.clear()  # pyright: ignore[reportPrivateUsage]
    gc.collect()
    for obj in gc.get_objects():
        if isinstance(obj, BaseTerm):
            obj._bzla = None  # pyright: ignore[reportPrivateUsage]
    yield


### ### ### ### ###

from pathlib import Path

from pyinstrument.profiler import Profiler
from pyinstrument.renderers.speedscope import SpeedscopeRenderer
from pyinstrument.session import Session

PROFILE_ROOT = Path.cwd() / ".profiles"

RENDER_OPTS: dict[str, dict[str, str | int]] = {
    "processor_options": {
        "filter_threshold": 0,
        "show_regex": r".*",
    },
}

combined = None


# https://pyinstrument.readthedocs.io/en/latest/guide.html#profile-pytest-tests
@pytest.fixture(autouse=True)
def pyinstrument_single(request: Any, reset_bitwuzla: Any) -> Iterator[None]:
    if not request.config.getoption("profile"):
        yield
        return

    profiler = Profiler()

    profiler.start()
    yield  # run test
    session = profiler.stop()

    global combined
    if combined is None:
        combined = session
    else:
        combined = Session.combine(combined, session)

    filename = PROFILE_ROOT / f"{request.node.name}.json"
    renderer = SpeedscopeRenderer(**RENDER_OPTS)
    with open(filename, "w", encoding="utf-8") as f:
        f.write(renderer.render(session))


@pytest.fixture(scope="session", autouse=True)
def pyinstrument_combined(pytestconfig: pytest.Config) -> Iterator[None]:
    if not pytestconfig.getoption("profile"):
        yield
        return

    PROFILE_ROOT.mkdir(exist_ok=True)
    for path in PROFILE_ROOT.glob("*.json"):
        if path.is_file():
            path.unlink()

    yield  # run test suite

    if combined is not None:
        filename = PROFILE_ROOT / "combined.json"
        renderer = SpeedscopeRenderer(**RENDER_OPTS)
        with open(filename, "w", encoding="utf-8") as f:
            f.write(renderer.render(combined))


### ### ### ### ###

import tracemalloc

from _pytest.fixtures import SubRequest

import zoology

_memory_stats: dict[SubRequest, int] = {}
_state_stats: dict[SubRequest, tuple[int, int]] = {}


@pytest.fixture(autouse=True)
def track_memory_usage(request: SubRequest, reset_bitwuzla: Any) -> Iterator[None]:
    """
    Track peak memory usage during test execution.

    Warning: only tracks allocations made by Python code, not memory usage of
    subprocesses or (probably) memory allocated by C extensions.
    """
    if not request.config.getoption("memory"):
        yield
        return

    tracemalloc.start()
    yield  # run test
    _, peak = tracemalloc.get_traced_memory()
    _memory_stats[request] = peak
    tracemalloc.stop()


@pytest.fixture(autouse=True)
def track_candidates_checked(request: SubRequest) -> Iterator[None]:
    """Track application counters during test execution."""
    zoology.count = 0
    smt.checks = 0
    yield  # run test
    if zoology.count:
        _state_stats[request] = (zoology.count, smt.checks)


def pytest_terminal_summary(terminalreporter: pytest.TerminalReporter) -> None:
    if _memory_stats:
        terminalreporter.line("")
        terminalreporter.section("peak memory usage")
        for request, peak in sorted(_memory_stats.items(), key=lambda x: -x[1]):
            terminalreporter.write(
                "% 5d MiB      %s\n" % (peak // 1024 // 1024, request.node.nodeid)
            )
    if _state_stats:
        terminalreporter.line("")
        terminalreporter.section("candidates checked")
        for request, (n, _) in sorted(_state_stats.items(), key=lambda x: -x[1][0]):
            terminalreporter.write("% 5d          %s\n" % (n, request.node.nodeid))
        terminalreporter.line("")
        terminalreporter.section("solver calls")
        for request, (_, n) in sorted(_state_stats.items(), key=lambda x: -x[1][1]):
            terminalreporter.write("% 5d          %s\n" % (n, request.node.nodeid))


### ### ### ### ###

from . import solidity

solidity.install_solidity()
