# ruff: noqa: E402

# Provide smart debug info for assertions that appear in these non-test modules.
# Must appear *before* the module is imported. See:
# https://docs.pytest.org/en/latest/how-to/assert.html#assert-introspection

import pytest

pytest.register_assert_rewrite("helpers", "solidity")

### ### ### ### ###

from pathlib import Path
from typing import Any, Iterator, cast

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


def pytest_addoption(
    parser: pytest.Parser, pluginmanager: pytest.PytestPluginManager
) -> None:
    parser.addoption("--profile", dest="profile", action="store_true")


# https://pyinstrument.readthedocs.io/en/latest/guide.html#profile-pytest-tests
@pytest.fixture(autouse=True)
def pyinstrument_single(
    request: Any,
    reset_bitwuzla: None,  # reset *before* starting profiler
) -> Iterator[None]:
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


### ### ### ###

import gc

from zbitvector._bitwuzla import BZLA, CACHE, Array, Constraint, Option, Symbolic, Uint

# pyright: reportPrivateUsage=false


@pytest.fixture(autouse=True)
def reset_bitwuzla() -> Iterator[None]:
    """
    Reinitialize the Bitwuzla solver and migrate constants to the new solver.

    Without this optimization, Bitwuzla state is not garbage-collected and long
    test runs can be ~8x slower.
    """
    CACHE.clear()
    gc.collect()

    bsort: list[tuple[type[Symbolic], int]] = []
    asort: list[tuple[type[Array[Any, Any]], int, int]] = []

    for cls in cast("list[type[Symbolic]]", Uint.__subclasses__()):
        bsort.append((cls, cls._sort.bv_get_size()))

    for cls in cast(
        "list[type[Array[Any, Any]]]", Array.__subclasses__() + Array.__subclasses__()
    ):
        if not hasattr(cls, "_sort"):
            continue
        k: int = cls._sort.array_get_index().bv_get_size()
        v: int = cls._sort.array_get_element().bv_get_size()
        asort.append((cls, k, v))

    BZLA.check_sat()
    bitem: list[tuple[Symbolic, int]] = []
    aitem: list[tuple[Array[Any, Any], int]] = []
    for obj in gc.get_objects():
        if isinstance(obj, Symbolic):
            if not obj._term.is_bv_value():
                continue
            s = BZLA.get_value_str(obj._term)
            bitem.append((obj, int(s, 2)))
        elif isinstance(obj, Array):
            obj = cast("Array[Any, Any]", obj)
            if not obj._term.is_const_array():
                continue
            s = BZLA.get_value_str(obj._term.get_children()[0])
            aitem.append((obj, int(s, 2)))

    BZLA.__init__()
    BZLA.set_option(Option.INCREMENTAL, True)
    BZLA.set_option(Option.PRODUCE_MODELS, True)
    BZLA.set_option(Option.OUTPUT_NUMBER_FORMAT, "hex")
    BZLA.check_sat()

    Constraint._sort = BZLA.mk_bool_sort()
    for cls, n in bsort:
        cls._sort = BZLA.mk_bv_sort(n)
    for cls, k, v in asort:
        cls._sort = BZLA.mk_array_sort(BZLA.mk_bv_sort(k), BZLA.mk_bv_sort(v))
    for b, s in bitem:
        b._term = BZLA.mk_bv_value(b._sort, s)
    for a, s in aitem:
        a._term = BZLA.mk_const_array(a._sort, a._value(s)._term)

    yield


### ### ### ### ###

from . import solidity

solidity.install_solidity()
