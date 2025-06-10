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

    @classmethod
    def dump(cls) -> str:
        """Write out `composite.py`."""
        cls.out = bytearray()
        cls._dump()
        formatted = check_output(["ruff", "format", "-"], input=cls.out)
        return formatted.decode()

    @classmethod
    def _dump(cls) -> None:
        cls.out.extend(b"""\"""
High-level SMT library with full term rewriting.

Warning: do not edit! To regenerate, run:

    $ python -m smt2.analyze_composite

\"""
# ruff: noqa: D101, D102, D103

from __future__ import annotations

import abc
from dataclasses import InitVar, dataclass, field
from functools import reduce
from typing import Any, ClassVar, override

from .theory_core import BaseTerm, DumpContext

type MinMax = tuple[int, int]

""")
        cls._source(RewriteMeta)
        cls._theory(theory_core)
        cls._theory(theory_bitvec)
        cls._theory(theory_array)
        cls._rewrites(rewrite)
        cls._source(propagate_minmax)
        cls._source(constraint_minmax)

    @classmethod
    def _theory(cls, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isinstance(item, type) or not issubclass(item, BaseTerm):
                continue
            elif item == BaseTerm or getmodule(item) != module:
                continue
            cls._source(item)

    @classmethod
    def _rewrites(cls, module: ModuleType) -> None:
        for item in vars(module).values():
            if not isfunction(item) or getmodule(item) != module:
                continue
            cls._source(item)

    @classmethod
    def _source(cls, object: type | Callable[..., Any]) -> None:
        s = getsource(object)
        # Inject metaclass for constraints & bitvectors
        s = re.sub(r"(CTerm|BTerm)\(BaseTerm", r"\1(BaseTerm, metaclass=RewriteMeta", s)
        # Delete docstrings, comments
        s = re.sub(r'\n*\s*("""[^"]*"""| #.*)\n+', "\n", s)
        # Skip unimplemented rewrite cases
        s = re.sub(r"\n*\s*case [^_].*\n\s*raise NotImplementedError", "", s)
        cls.out.extend(s.encode())
        cls.out.extend(b"\n")


if __name__ == "__main__":
    with open(COMPOSITE_PY, "w") as f:
        f.write(Compositor().dump())
