"""Wrapper around pybitwuzla for state management."""

import gc
from collections import defaultdict
from typing import Any
from weakref import WeakValueDictionary

from pybitwuzla import Bitwuzla, BitwuzlaSort, BitwuzlaTerm, Kind, Option, Result

_bzla = Bitwuzla()
_checked = 0
_cache: dict[Any, dict[Any, Any]] = defaultdict(dict)
_sorts: dict[int, BitwuzlaSort] = {}


def reset() -> None:
    """Reset the global Bitwuzla instance."""
    global _bzla, _cache, _checked, _sorts

    _bzla = Bitwuzla()
    _bzla.set_option(Option.INCREMENTAL, True)
    _bzla.set_option(Option.PRODUCE_MODELS, True)

    tmp: dict[Any, WeakValueDictionary[Any, Any]] = defaultdict(WeakValueDictionary)
    for cls, subcache in _cache.items():
        for k, v in subcache.items():
            tmp[cls][k] = v

    _cache = defaultdict(dict)
    _checked = 0

    _sorts = {}
    for i in [1, 8, 128, 160, 256, 257, 512]:
        _sorts[i] = _bzla.mk_bv_sort(i)

    gc.collect()
    for cls, args in tmp.items():
        for arg in args.keys():
            args[arg].node = cls(arg).node
            _cache[cls][arg] = args[arg]


reset()


def sort(width: int) -> BitwuzlaSort:
    """Retrieve the bitvector sort of the given width."""
    return _sorts[width]


def cache() -> dict[Any, dict[Any, Any]]:
    """Retrieve the internal cache."""
    return _cache


def mk_term(
    kind: Kind, terms: list[BitwuzlaTerm], indices: list[int] | None = None
) -> BitwuzlaTerm:
    """Create a new term."""
    return _bzla.mk_term(kind, terms, indices)


def mk_const(sort: BitwuzlaSort, symbol: str) -> BitwuzlaTerm:
    """Create a new constant."""
    return _bzla.mk_const(sort, symbol)


def mk_bv_value(sort: BitwuzlaSort, value: int) -> BitwuzlaTerm:
    """Create a bitvector value."""
    return _bzla.mk_bv_value(sort, value)


def assume_formula(*args: BitwuzlaTerm) -> None:
    """Temporarily add a formula to the solver."""
    _bzla.assume_formula(*args)


def check_sat() -> Result:
    """Invoke the solver."""
    global _checked
    result = _bzla.check_sat()
    _checked = 2 if result == Result.SAT else 0
    return result


def get_unsat_assumptions() -> list[BitwuzlaTerm]:
    """Compute the unsatisfiable core."""
    return list(_bzla.get_unsat_assumptions())


def get_value(term: BitwuzlaTerm) -> BitwuzlaTerm:
    """Load a value from the solver."""
    assert _checked == 2
    return _bzla.get_value(term)


def get_value_int(term: BitwuzlaTerm) -> int:
    """Load a value from the solver as an int."""
    global _checked
    if _checked == 0:
        assert _bzla.check_sat() == Result.SAT
        _checked = 1
    return int(_bzla.get_value_str(term), 2)


def mk_bv_sort(width: int) -> BitwuzlaSort:
    """Create a bitvector sort of arbitrary width."""
    return _bzla.mk_bv_sort(width)


def mk_array_sort(index: BitwuzlaSort, elem: BitwuzlaSort) -> BitwuzlaSort:
    """Create an array sort."""
    return _bzla.mk_array_sort(index, elem)


def mk_const_array(sort: BitwuzlaSort, value: BitwuzlaTerm) -> BitwuzlaTerm:
    """Create a const array."""
    return _bzla.mk_const_array(sort, value)
