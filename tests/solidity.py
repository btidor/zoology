"""Helpers for working with Solidity fixtures in tests."""

import os
import re
import subprocess
from enum import Enum
from pathlib import Path

from disassembler import Program, disassemble


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
        code = f.read()
    return disassemble(code)


def compile_solidity(source: str) -> dict[str, bytes]:
    """Return the binary contract code for each contract in the source file."""
    version = _detect_version(source)

    env = os.environ.copy()
    env["SOLC_VERSION"] = version.value
    output = subprocess.check_output(
        ["solc", "--bin-runtime", "-"], env=env, input=source.encode()
    ).splitlines()

    current = "<unknown>"
    matches: dict[str, bytes] = {}
    for i in range(len(output)):
        if output[i].startswith(b"======="):
            current = output[i].split(b" ")[1][8:].decode()
        if output[i] == b"Binary of the runtime part:":
            matches[current] = bytes.fromhex(output[i + 1].decode())
    return matches


def _detect_version(source: str) -> Solidity:
    match = re.search("^\\s*pragma solidity (.*);$", source, re.M)
    if match is None:
        raise ValueError(f"could not extract compiler version")

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
