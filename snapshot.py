#!/usr/bin/env python3
"""A client for the Ethereum JSON-RPC API."""

import json
from pathlib import Path
from time import sleep

import requests

from bytes import Bytes
from disassembler import disassemble
from environment import Contract
from smt import Uint160, Uint256

# For consistency, make requests at a fixed block offset
TAG = "0x574800"

COUNT = 32

_ROOT = Path(__file__).resolve().parent

_apikey: str | None = None

type Snapshot = dict[str, dict[str, str]]

PLAYER = Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
PROXY = Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)


with open(_ROOT / "ethernaut.json") as f:
    _eth = json.load(f)
    LEVEL_FACTORIES = [
        Uint160(int.from_bytes(bytes.fromhex(_eth[str(i)][2:]))) for i in range(COUNT)
    ]

cache: Snapshot | None = None


def snapshot_contracts(address: Uint160, invisible: bool = True) -> dict[int, Contract]:
    """Load the given contract from the snapshot, and any contracts it references."""
    global cache
    if cache is None:
        with open(_ROOT / "snapshot.json") as f:
            cache = json.load(f)
        assert cache is not None

    assert (a := address.reveal()) is not None
    saved = cache[a.to_bytes(20).hex()]
    address = Uint160(a)
    program = disassemble(Bytes.fromhex(saved["code"]))
    # ASSUMPTION: no solution requires interacting with the factory contract.
    contract = Contract(address=address, program=program, invisible=invisible)
    contracts = dict[int, Contract]()

    for k, v in saved.items():
        if k == "code":
            continue
        contract.storage[Uint256(int(k))] = Uint256(int(v, 16))
        if is_sibling_contract(int(k), int(v, 16)):
            # Warning! Levels like Delegation include global non-factory
            # contracts that *do* need to be interacted with.
            contracts.update(snapshot_contracts(Uint160(int(v, 16)), False))

    # Some level factories create other contracts in their constructor. To avoid
    # address collisions between these fixed contracts and created level
    # contracts, bump up the nonce.
    contract.nonce = Uint256(16)
    contracts[a] = contract
    return contracts


def get_code(address: Uint160) -> Contract:
    """Load the Contract at a given address."""
    assert (a := address.reveal()) is not None
    data = _api_request("eth_getCode", address=a.to_bytes(20).hex(), tag=TAG)
    program = disassemble(Bytes(data))
    return Contract(address=address, program=program)


def get_storage_at(address: Uint160, position: Uint256) -> Uint256:
    """Load the contents of a given storage slot."""
    assert (a := address.reveal()) is not None
    assert (p := position.reveal()) is not None
    value = _api_request(
        "eth_getStorageAt",
        address=a.to_bytes(20).hex(),
        position=p.to_bytes(32).hex(),
        tag=TAG,
    )
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
            "https://api-sepolia.etherscan.io/api",
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


def download_contract(snapshot: Snapshot, address: Uint160) -> None:
    """Download a given address's code and data."""
    assert (a := address.reveal()) is not None
    contract = get_code(address)
    assert (c := contract.program.code.reveal()) is not None
    snapshot[a.to_bytes(20).hex()] = {"code": c.hex()}

    for j in range(8):
        # HACK: level factories only use the first few storage slots. Higher
        # slots are for maps keyed by player, which we can initialize to
        # zero.
        storage = get_storage_at(address, Uint256(j))
        assert (v := storage.reveal()) is not None
        if v != 0:
            snapshot[a.to_bytes(20).hex()][str(j)] = v.to_bytes(32).hex()
        if j > 0 and v > 2**156 and v < 2**160:
            # The Level interface puts the owner in Slot 0; skip it.
            download_contract(snapshot, Uint160(v))
        if is_sibling_contract(j, v):
            download_contract(snapshot, Uint160(v))


def is_sibling_contract(slot: int, value: int) -> bool:
    """Check if a given storage slot refers to a related contract."""
    # The Level interface puts the owner in Slot 0; skip it.
    return slot > 0 and value > 2**156 and value < 2**160


if __name__ == "__main__":
    snapshot: Snapshot = {}
    for i, address in enumerate(LEVEL_FACTORIES):
        print(f"Downloading level {i} of {COUNT-1}")
        download_contract(snapshot, address)
    with open(_ROOT / "snapshot.json", "w") as f:
        json.dump(snapshot, f, indent=4)
        f.write("\n")
