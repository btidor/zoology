"""
Code generation for the composite SMT library.

Takes the low-level library defined in `theory_*.py`, combines it with the rules
from the rewrite library, and outputs to `composite.py`.
"""

from __future__ import annotations

import re
from inspect import getmodule, getsource, isfunction
from pathlib import Path
from subprocess import check_output
from types import ModuleType
from typing import Any, Callable

from . import rewrite, theory_array, theory_bitvec, theory_core
from .minmax import RewriteMeta, constraint_minmax, propagate_minmax
from .theory_core import BaseTerm

COMPOSITE_PY = Path(__file__).parent / "composite.py"


class Compositor:
    """Produces a high-level SMT library by composing low-level components."""

    def dump(self) -> bytes:
        """Write out `composite.py`."""
        self.out = bytearray()
        self._dump()
        return check_output(["ruff", "format", "-"], input=self.out)

    def _dump(self) -> None:
        self.out.extend(b"""\"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analyze_composite

\"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
import copy
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, Self, override

from .theory_core import BaseTerm, DumpContext

type MinMax = tuple[int, int]

""")
        self._source(RewriteMeta)
        self._theory(theory_core)
        self._theory(theory_bitvec)
        self._theory(theory_array)
        self._rewrites(rewrite)
        self._source(propagate_minmax)
        self._source(constraint_minmax)

    def _theory(self, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isinstance(item, type) or not issubclass(item, BaseTerm):
                continue
            elif item == BaseTerm or getmodule(item) != module:
                continue
            self._source(item)

    def _rewrites(self, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isfunction(item) or getmodule(item) != module:
                continue
            self._source(item)

    def _source(self, object: type | Callable[..., Any]) -> None:
        s = getsource(object)
        # Inject metaclass for constraints & bitvectors
        s = re.sub(r"(CTerm|BTerm)\(BaseTerm", r"\1(BaseTerm, metaclass=RewriteMeta", s)
        # Delete docstrings, comments
        s = re.sub(r'\n*\s*("""[^"]*"""| # (?!pyright:).*)\n+', "\n", s)
        # Skip unimplemented rewrite cases
        s = re.sub(r"\n*\s*case [^_].*\n\s*raise NotImplementedError", "", s)
        self.out.extend(s.encode())
        self.out.extend(b"\n")


if __name__ == "__main__":
    r = Compositor().dump()
    with open(COMPOSITE_PY, "wb") as f:
        f.write(r)
