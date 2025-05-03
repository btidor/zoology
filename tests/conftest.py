# ruff: noqa: E402

# Provide smart debug info for assertions that appear in these non-test modules.
# Must appear *before* the module is imported. See:
# https://docs.pytest.org/en/latest/how-to/assert.html#assert-introspection

import pytest

pytest.register_assert_rewrite("helpers", "solidity")

### ### ### ### ###

from pathlib import Path
from typing import Any, Iterator

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


### ### ### ### ###

from . import solidity

solidity.install_solidity()
