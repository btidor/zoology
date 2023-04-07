#!/usr/bin/env python3
"""A client for the Ethereum JSON-RPC API."""

import requests

from arrays import Array
from disassembler import disassemble
from environment import Contract
from smt import Uint160, Uint256

# For now, make requests for a given, fixed block offset.
TAG = "0x81f21d"

with open(".key") as f:
    API_KEY = f.read().strip()


def get_code(address: Uint160) -> Contract:
    """Load the Contract at a given address."""
    code = _api_request(
        "eth_getCode",
        address=address.unwrap(bytes).hex(),
        tag=TAG,
    )
    program = disassemble(code)
    return Contract(address, program, Array.concrete(Uint256, Uint256(0)))


def get_storage_at(address: Uint160, position: Uint256) -> Uint256:
    """Load the contents of a given storage slot."""
    value = _api_request(
        "eth_getStorageAt",
        address=address.unwrap(bytes).hex(),
        position=position.unwrap(bytes).hex(),
        tag=TAG,
    )
    return Uint256(int.from_bytes(value))


def _api_request(action: str, **kwargs: str) -> bytes:
    res = requests.get(
        "https://api-goerli.etherscan.io/api",
        {
            **kwargs,
            "module": "proxy",
            "action": action,
            "apikey": API_KEY,
        },
        headers={
            "User-Agent": "zoonaut",
        },
    )
    res.raise_for_status()
    assert "error" not in res.json(), res.json()["error"]["message"]
    result = res.json()["result"]
    if result[:2] != "0x":
        raise ValueError(result)
    return bytes.fromhex(result[2:])


if __name__ == "__main__":
    print(get_code(Uint160(0xD2E5E0102E55A5234379DD796B8C641CD5996EFD)))
    print(
        get_storage_at(
            Uint160(0xD2E5E0102E55A5234379DD796B8C641CD5996EFD),
            Uint256(0xD362A90B918E441DEC884EE15A0F6D394D7875F3929A29069CD25AFF7D935874),
        ).describe()
    )
