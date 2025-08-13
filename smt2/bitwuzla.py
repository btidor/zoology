"""A wrapper for the Bitwuzla SMT backend."""
# ruff: noqa: D101, D102, D103, D107

from __future__ import annotations

from typing import Any, overload

from zbitvector.pybitwuzla import (
    Bitwuzla,
    BitwuzlaSort,
    BitwuzlaTerm,
    Kind,
    Option,
    Result,
)

type SortWidth = None | int | tuple[int, int]


class BitwuzlaManager:
    """Manages access to the global Bitwuzla instance."""

    _bzla: Bitwuzla
    _sort: dict[SortWidth, BitwuzlaSort]
    _sym: dict[bytes, tuple[SortWidth, BitwuzlaTerm]]

    # For convenience, centralize all global state here.
    special: dict[Any, Any]  # for CacheMeta
    last_solver: Any  # for Solver

    def __init__(self):
        self._sort = {}
        self._sym = {}
        self.special = {}
        self.last_solver = None
        self.reset()

    def reset(self) -> None:
        self._bzla = Bitwuzla()
        self._bzla.set_option(Option.INCREMENTAL, True)
        self._bzla.set_option(Option.PRODUCE_MODELS, True)
        self._bzla.set_option(Option.OUTPUT_NUMBER_FORMAT, "hex")
        self._sort.clear()
        self._sym.clear()
        self.special.clear()
        self.last_solver = None

    def mk_term(
        self,
        kind: Kind,
        terms: list[BitwuzlaTerm] | tuple[BitwuzlaTerm, ...],
        indices: list[int] | tuple[int, ...] | None = None,
    ) -> BitwuzlaTerm:
        return self._bzla.mk_term(kind, terms, indices)

    def mk_sort(self, width: SortWidth) -> BitwuzlaSort:
        if width not in self._sort:
            match width:
                case None:
                    s = self._bzla.mk_bool_sort()
                case int() as width:
                    s = self._bzla.mk_bv_sort(width)
                case (k, v):
                    s = self._bzla.mk_array_sort(self.mk_sort(k), self.mk_sort(v))
            self._sort[width] = s
        return self._sort[width]

    def mk_symbol(self, name: bytes, width: SortWidth) -> BitwuzlaTerm:
        if name not in self._sym:
            self._sym[name] = (width, self._bzla.mk_const(self.mk_sort(width)))
        orig, term = self._sym[name]
        assert width == orig, f"symbol already used: {name}"
        return term

    @overload
    def mk_value(self, value: bool, width: None) -> BitwuzlaTerm: ...
    @overload
    def mk_value(self, value: int, width: int) -> BitwuzlaTerm: ...
    @overload
    def mk_value(self, value: BitwuzlaTerm, width: tuple[int, int]) -> BitwuzlaTerm: ...
    def mk_value(
        self, value: bool | int | BitwuzlaTerm, width: SortWidth
    ) -> BitwuzlaTerm:
        sort = self.mk_sort(width)
        match width:
            case None:
                assert isinstance(value, bool)
                return self._bzla.mk_bv_value(sort, int(value))
            case int():
                assert isinstance(value, int)
                return self._bzla.mk_bv_value(sort, value)
            case (int(), int()):
                assert isinstance(value, BitwuzlaTerm)
                return self._bzla.mk_const_array(sort, value)

    def check(self, solver: Any, term: Any) -> bool:
        self.last_solver = solver
        self._bzla.assume_formula(term.bzla)
        match self._bzla.check_sat():
            case Result.SAT:
                return True
            case Result.UNSAT:
                return False
            case Result.UNKNOWN:
                raise RuntimeError

    def get_value_str(self, term: Any) -> str | dict[str, str]:
        return self._bzla.get_value_str(term.bzla)


BZLA = BitwuzlaManager()
