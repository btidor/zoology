#!/usr/bin/env python3
"""A client for the Ethereum JSON-RPC API."""

import json
from pathlib import Path
from time import sleep

import requests

from disassembler import disassemble
from environment import Contract, Universe
from smt.smt import Uint160, Uint256

# For consistency, make requests at a fixed block offset
TAG = "0x86a800"

_ROOT = Path(__file__).resolve().parent

_apikey: str | None = None


with open(_ROOT / "ethernaut.json") as f:
    _eth = json.load(f)
    LEVEL_FACTORIES = [
        Uint160(int.from_bytes(bytes.fromhex(_eth[str(i)][2:]))) for i in range(29)
    ]


def apply_snapshot(universe: Universe) -> None:
    """Load a snapshot and add the contracts to the given universe."""
    with open(_ROOT / "snapshot.json") as f:
        snapshot = json.load(f)
    for addr, saved in snapshot.items():
        address = Uint160(int(addr, 16))
        program = disassemble(bytes.fromhex(saved["code"]))
        contract = Contract(address, program)

        for k, v in saved.items():
            if k == "code":
                continue
            contract.storage.poke(Uint256(int(k)), Uint256(int(v, 16)))

        universe.add_contract(contract)
        universe.balances[contract.address] = Uint256(0)


def get_code(address: Uint160) -> Contract:
    """Load the Contract at a given address."""
    assert (a := address.maybe_unwrap(bytes)) is not None
    code = _api_request("eth_getCode", address=a.hex(), tag=TAG)
    program = disassemble(code)
    return Contract(address, program)


def get_storage_at(address: Uint160, position: Uint256) -> Uint256:
    """Load the contents of a given storage slot."""
    assert (a := address.maybe_unwrap(bytes)) is not None
    assert (p := position.maybe_unwrap(bytes)) is not None
    value = _api_request("eth_getStorageAt", address=a.hex(), position=p.hex(), tag=TAG)
    return Uint256(int.from_bytes(value))


def _api_request(action: str, **kwargs: str) -> bytes:
    global _apikey
    if _apikey is None:
        with open(_ROOT / ".key") as f:
            _apikey = f.read().strip()

    i = 0
    while True:
        i += 1
        res = requests.get(
            "https://api-goerli.etherscan.io/api",
            {
                **kwargs,
                "module": "proxy",
                "action": action,
                "apikey": _apikey,
            },
            headers={
                "User-Agent": "zoology",
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
    snapshot = {}
    for i, address in enumerate(LEVEL_FACTORIES):
        print(f"Downloading level {i}")
        assert (a := address.maybe_unwrap(bytes)) is not None
        contract = get_code(address)
        assert (c := contract.program.code.maybe_unwrap()) is not None
        snapshot[a.hex()] = {"code": c.hex()}

        for j in range(8):
            # HACK: level factories only use the first few storage slots. Higher
            # slots are for maps keyed by player, which we can initialize to
            # zero.
            storage = get_storage_at(address, Uint256(j))
            assert (v := storage.maybe_unwrap(bytes)) is not None
            if int.from_bytes(v) != 0:
                snapshot[a.hex()][str(j)] = v.hex()

        # TODO: some level factories reference other contracts (e.g. via storage
        # slots), we may need to include those as well.

    with open(_ROOT / "snapshot.json", "w") as f:
        json.dump(snapshot, f, indent=4)
        f.write("\n")
