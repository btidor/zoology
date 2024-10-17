#!/usr/bin/env python3
"""An out-of-process SMT solver based on the zbitvector backend."""

import copy
import math
import os
import subprocess
import sys
from enum import Enum
from io import BytesIO
from tempfile import gettempdir
from typing import IO, Any, Self

from zbitvector import _bitwuzla
from zbitvector._bitwuzla import BZLA, BitwuzlaSort, BitwuzlaTerm, Kind, Result


class Special(Enum):
    """A supplement to pybitwuzla.Kind."""

    ASSERT = 255
    CHECK = 254
    EVALUATE = 253
    FORK = 252

    ARRAY_SORT = 249
    BV_SORT = 248


class Client:
    """A client for communicating with the solver process."""

    def __init__(self) -> None:
        """Create a new Client."""
        self._terms = dict[BitwuzlaTerm, int]()
        self._sorts = dict[int | tuple[int, int], int]()
        self._counter = 1

        pa, pb = self._setup()
        subprocess.Popen([__file__, self._prefix])
        self._out = open(pa, "wb")
        self._in = open(pb, "rb")

    def __deepcopy__(self, memo: Any) -> Self:
        result = self.__new__(self.__class__)
        result._terms = copy.copy(self._terms)
        result._sorts = copy.copy(self._sorts)
        result._counter = self._counter

        pa, pb = self._setup()
        _write_kind(self._out, Special.FORK)
        _write_str(self._out, result._prefix)
        self._out.flush()
        result._out = open(pa, "wb")
        result._in = open(pb, "rb")
        return result

    def _setup(self) -> tuple[str, str]:
        self._prefix = os.urandom(8).hex()
        paths = _paths_for(self._prefix)
        for p in paths:
            os.mkfifo(p)
        return paths

    def add_term(self, term: BitwuzlaTerm) -> int:
        """Register a term with the server and return its ID."""
        if term in self._terms:
            return self._terms[term]

        with BytesIO() as buf:
            kind = term.get_kind()
            _write_kind(buf, kind)
            match kind:
                case Kind.VAL:
                    if _bitwuzla.last_check is False:
                        assert BZLA.check_sat() == Result.SAT
                        _bitwuzla.last_check = True
                    sort = term.get_sort()
                    _write_id(buf, self.add_sort(sort))
                    _write_bv(buf, sort, int(BZLA.get_value_str(term), 2))
                case Kind.CONST:
                    _write_id(buf, self.add_sort(term.get_sort()))
                    assert (sym := term.get_symbol()) is not None
                    _write_str(buf, sym)
                case Kind.CONST_ARRAY:
                    _write_id(buf, self.add_sort(term.get_sort()))
                    default = term.get_children()[0]
                    _write_id(buf, self.add_term(default))
                case _:
                    terms = term.get_children()
                    _write_size(buf, len(terms))
                    for t in terms:
                        _write_id(buf, self.add_term(t))
                    if term.is_indexed():
                        indices = term.get_indices()
                        _write_size(buf, len(indices))
                        for i in indices:
                            _write_index(buf, i)
                    else:
                        _write_size(buf, 0)
            self._out.write(buf.getbuffer())

        self._terms[term] = self._counter
        self._counter += 1
        return self._terms[term]

    def add_sort(self, sort: BitwuzlaSort) -> int:
        """Register a sort with the server and return its ID."""
        if sort.is_array():
            k = self.add_sort(sort.array_get_index())
            v = self.add_sort(sort.array_get_element())
            if (k, v) in self._sorts:
                return self._sorts[(k, v)]

            _write_kind(self._out, Special.ARRAY_SORT)
            _write_id(self._out, k)
            _write_id(self._out, v)
            self._sorts[(k, v)] = self._counter
            self._counter += 1
            return self._sorts[(k, v)]
        elif sort.is_bv():
            n = sort.bv_get_size()
            if n in self._sorts:
                return self._sorts[n]

            _write_kind(self._out, Special.BV_SORT)
            _write_index(self._out, n)
            self._sorts[n] = self._counter
            self._counter += 1
            return self._sorts[n]
        else:
            raise NotImplementedError(f"unsupported sort: {sort}")

    def assert_term(self, term: BitwuzlaTerm) -> None:
        """Permanently assert the given expression."""
        id = self.add_term(term)
        _write_kind(self._out, Special.ASSERT)
        _write_id(self._out, id)

    def check(self, term: BitwuzlaTerm) -> bool:
        """Check whether the given boolean term is satisfiable."""
        id = self.add_term(term)
        _write_kind(self._out, Special.CHECK)
        _write_id(self._out, id)
        self._out.flush()
        return bool(_read_index(self._in))

    def evaluate(self, term: BitwuzlaTerm) -> int:
        """Return a value for the given term."""
        id = self.add_term(term)
        _write_kind(self._out, Special.EVALUATE)
        _write_id(self._out, id)
        self._out.flush()
        return _read_bv(self._in, term.get_sort())

    def close(self) -> None:
        """Terminate the solver."""
        for p in (self._out, self._in):
            p.close()


class Server:
    """The out-of-process solver."""

    def __init__(self, prefix: str) -> None:
        """Create a new Server."""
        self._items = dict[int, BitwuzlaTerm | BitwuzlaSort]()
        self._counter = 1
        self._open(prefix)

    def handle_request(self) -> None:
        """Process a single message from the client."""
        match _read_kind(self._in):
            case Special.ASSERT:
                term = _read_term(self._in, self._items)
                assert term.is_bv() and term.get_sort().bv_get_size() == 1
                BZLA.assert_formula(term)
                return
            case Special.CHECK:
                term = _read_term(self._in, self._items)
                assert term.is_bv() and term.get_sort().bv_get_size() == 1
                BZLA.assume_formula(term)
                match BZLA.check_sat():
                    case Result.SAT:
                        _write_index(self._out, 1)
                    case Result.UNSAT:
                        _write_index(self._out, 0)
                    case Result.UNKNOWN:
                        raise RuntimeError("Bitwuzla could not solve this instance")
                self._out.flush()
                return
            case Special.EVALUATE:
                term = _read_term(self._in, self._items)
                assert term.is_bv()
                _write_bv(self._out, term.get_sort(), int(BZLA.get_value_str(term), 2))
                self._out.flush()
                return
            case Special.FORK:
                prefix = _read_str(self._in)
                if os.fork() == 0:
                    for p in (self._out, self._in):
                        p.close()
                    self._open(prefix)
                return
            case Special.ARRAY_SORT:
                result = BZLA.mk_array_sort(
                    _read_sort(self._in, self._items), _read_sort(self._in, self._items)
                )
            case Special.BV_SORT:
                result = BZLA.mk_bv_sort(_read_index(self._in))
            case Kind.VAL:
                sort = _read_sort(self._in, self._items)
                result = BZLA.mk_bv_value(sort, _read_bv(self._in, sort))
            case Kind.CONST:
                result = BZLA.mk_const(
                    _read_sort(self._in, self._items), _read_str(self._in)
                )
            case Kind.CONST_ARRAY:
                result = BZLA.mk_const_array(
                    _read_sort(self._in, self._items), _read_term(self._in, self._items)
                )
            case kind:
                terms = [
                    _read_term(self._in, self._items)
                    for _ in range(_read_size(self._in))
                ]
                indices = tuple(
                    _read_index(self._in) for _ in range(_read_size(self._in))
                )
                result = BZLA.mk_term(kind, terms, indices if indices else None)
        self._items[self._counter] = result
        self._counter += 1

    def _open(self, prefix: str) -> None:
        self._prefix = prefix
        pa, pb = _paths_for(self._prefix)
        self._in = open(pa, "rb")
        self._out = open(pb, "wb")

    def close(self):
        """Terminate the solver."""
        for p in (self._in, self._out):
            p.close()
        for p in _paths_for(self._prefix):
            os.remove(p)


def _read(pipe: IO[bytes], size: int) -> bytes:
    data = pipe.read(size)
    if len(data) < size:
        raise EOFError
    return data


def _write_kind(pipe: IO[bytes], kind: Kind | Special) -> None:
    pipe.write(kind.value.to_bytes(1))


def _read_kind(pipe: IO[bytes]) -> Kind | Special:
    k = int.from_bytes(_read(pipe, 1))
    return Special(k) if k in Special else Kind(k)


def _write_index(pipe: IO[bytes], idx: int) -> None:
    pipe.write(idx.to_bytes(2))


def _read_index(pipe: IO[bytes]) -> int:
    return int.from_bytes(_read(pipe, 2))


def _write_id(pipe: IO[bytes], id: int) -> None:
    pipe.write(id.to_bytes(2))


def _read_term(
    pipe: IO[bytes], items: dict[int, BitwuzlaTerm | BitwuzlaSort]
) -> BitwuzlaTerm:
    item = items[int.from_bytes(_read(pipe, 2))]
    assert isinstance(item, BitwuzlaTerm)
    return item


def _read_sort(
    pipe: IO[bytes], items: dict[int, BitwuzlaTerm | BitwuzlaSort]
) -> BitwuzlaSort:
    item = items[int.from_bytes(_read(pipe, 2))]
    assert isinstance(item, BitwuzlaSort)
    return item


def _write_size(pipe: IO[bytes], id: int) -> None:
    pipe.write(id.to_bytes(2))


def _read_size(pipe: IO[bytes]) -> int:
    return int.from_bytes(_read(pipe, 2))


def _write_bv(pipe: IO[bytes], sort: BitwuzlaSort, val: int) -> None:
    assert sort.is_bv()
    b = math.ceil(sort.bv_get_size() / 8)
    pipe.write(val.to_bytes(b))


def _read_bv(pipe: IO[bytes], sort: BitwuzlaSort) -> int:
    assert sort.is_bv()
    b = math.ceil(sort.bv_get_size() / 8)
    return int.from_bytes(_read(pipe, b))


def _write_str(pipe: IO[bytes], s: str) -> None:
    data = s.encode()
    pipe.write(len(data).to_bytes(1))
    pipe.write(data)


def _read_str(pipe: IO[bytes]) -> str:
    n = int.from_bytes(_read(pipe, 1))
    return _read(pipe, n).decode()


def _paths_for(prefix: str) -> tuple[str, str]:
    c2s = os.path.join(gettempdir(), f"zoology-{prefix}-c2s")
    s2c = os.path.join(gettempdir(), f"zoology-{prefix}-s2c")
    return c2s, s2c


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} PREFIX")
        exit(1)

    server = Server(sys.argv[1])
    try:
        while True:
            server.handle_request()
    except (EOFError, KeyboardInterrupt):
        pass
    finally:
        server.close()
