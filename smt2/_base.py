"""TODO."""
# ruff: noqa

from __future__ import annotations

import abc
from dataclasses import dataclass, field
from typing import Any, Self


class Symbolic(abc.ABC):
    __slots__ = ()

    # Implementation Note: Symbolic instances are immutable. For performance,
    # don't copy them.
    def __copy__(self) -> Self:
        return self

    def __deepcopy__(self, memo: Any, /) -> Self:
        return self

    @abc.abstractmethod
    def _dump(self, ctx: DumpContext) -> None: ...


@dataclass
class DumpContext:
    out: bytearray = field(default_factory=bytearray)
    defs: dict[bytes, bytes] = field(default_factory=dict[bytes, bytes])

    def add(self, name: bytes, defn: bytes) -> None:
        assert name not in self.defs
        self.defs[name] = defn

    def write(self, b: bytes) -> None:
        self.out.extend(b)
