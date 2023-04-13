#!/usr/bin/env python3
"""A client for the Ethereum JSON-RPC API."""

import json
from time import sleep

import requests

from arrays import Array
from disassembler import disassemble
from environment import Contract
from smt import Uint160, Uint256

# For consistency, make requests at a fixed block offset
TAG = "0x86a800"

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
    i = 0
    while True:
        i += 1
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
            if result == "Max rate limit reached" and i < 3:
                sleep(1)
                continue
            raise ValueError(result)
        return bytes.fromhex(result[2:])


if __name__ == "__main__":
    with open("ethernaut.json") as f:
        data = json.load(f)
        factories = [
            Uint160(int.from_bytes(bytes.fromhex(data[str(i)][2:]))) for i in range(29)
        ]

    snapshot = {}
    for i, address in enumerate(factories):
        print(f"Downloading level {i}")
        key = address.unwrap(bytes).hex()
        contract = get_code(address)
        snapshot[key] = {"code": contract.program.code.unwrap().hex()}

        for j in range(8):
            # HACK: level factories only use the first few storage slots. Higher
            # slots are for maps keyed by player, which we can initialize to
            # zero.
            storage = get_storage_at(address, Uint256(j))
            if storage.unwrap(int) != 0:
                snapshot[key][str(j)] = storage.unwrap(bytes).hex()

        # TODO: some level factories reference other contracts (e.g. via storage
        # slots), we may need to include those as well.

    with open("snapshot.json", "w") as f:
        json.dump(snapshot, f, indent=4)
        f.write("\n")
