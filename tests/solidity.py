"""Helpers for working with Solidity fixtures in tests."""

import os
import re
import subprocess
from enum import Enum
from pathlib import Path

from bytes import Bytes
from disassembler import Program, disassemble
from environment import Contract, Universe
from sha3 import concrete_hash
from smt import Uint160


class Solidity(Enum):
    """Solidity compiler versions."""

    v08 = "0.8.17"
    v06 = "0.6.12"


_ROOT = Path(__file__).resolve().parent.parent


def load_solidity(path: str) -> Program:
    """Load a Solidity contract into a Program object."""
    assert path.endswith(".sol")
    with open(_ROOT / path, "r") as f:
        source = f.read()

    codes = compile_solidity(source)
    assert len(codes) == 1
    code = list(codes.values())[0]

    return disassemble(code)


def loads_solidity(path: str) -> dict[str, Program]:
    """Load a Solidity file containing multiple programs."""
    assert path.endswith(".sol")
    with open(_ROOT / path, "r") as f:
        source = f.read()

    codes = compile_solidity(source)
    return dict((name, disassemble(code)) for name, code in codes.items())


def load_binary(path: str) -> Program:
    """Load a file containing binary EVM contract code."""
    assert path.endswith(".bin")
    with open(_ROOT / path, "rb") as f:
        code = Bytes(f.read())
    return disassemble(code)


def universe_single(path: str) -> Universe:
    return Universe().with_contract(load_solidity(path))


def universe_binary(path: str) -> Universe:
    return Universe().with_contract(load_binary(path))


def universe_multiple(path: str) -> tuple[Universe, dict[str, Uint160]]:
    universe = Universe()
    addresses = dict[str, Uint160]()
    for name, program in loads_solidity(path).items():
        addresses[name] = concrete_hash(name).into(Uint160)
        universe = universe.with_contract(
            Contract(
                address=addresses[name],
                program=program,
            )
        )
    return universe, addresses


def compile_solidity(source: str) -> dict[str, Bytes]:
    """Return the binary contract code for each contract in the source file."""
    version = _detect_version(source)

    env = os.environ.copy()
    env["SOLC_VERSION"] = version.value
    output = subprocess.check_output(
        ["solc", "--bin-runtime", "-"], env=env, input=source.encode()
    ).splitlines()

    current = "<unknown>"
    matches = dict[str, Bytes]()
    for i in range(len(output)):
        if output[i].startswith(b"======="):
            current = output[i].split(b" ")[1][8:].decode()
        if output[i] == b"Binary of the runtime part:":
            matches[current] = Bytes.fromhex(output[i + 1].decode())
    return matches


def _detect_version(source: str) -> Solidity:
    match = re.search("^\\s*pragma solidity (.*);$", source, re.M)
    if match is None:
        raise ValueError("could not extract compiler version")

    version = match.group(1)
    if version.startswith("^0.8."):
        return Solidity.v08
    elif version.startswith("^0.6."):
        return Solidity.v06
    raise ValueError(f"unknown solidity version: {version}")


def install_solidity() -> None:
    """Use solc to install the expected versions of Solidity."""
    marker = Path.home() / ".config" / "solc-versions"
    target = [version.value for version in Solidity]
    if marker.exists():
        with open(marker) as f:
            if f.read() == str(target):
                return

    for version in Solidity:
        subprocess.check_call(["solc-select", "install", version.value])

    with open(marker, "w") as f:
        f.write(str(target))
