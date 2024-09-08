"""A client for the Ethereum JSON-RPC API."""

from __future__ import annotations

import json
from pathlib import Path
from time import sleep
from typing import TypeGuard

import requests

from bytes import Bytes
from disassembler import Program, disassemble
from smt import Uint256
from state import Address, Blockchain, Contract

# For consistency, make requests at a fixed block offset
TAG = "0x574800"

COUNT = 32

_ROOT = Path(__file__).resolve().parent

_apikey: str | None = None

type Snapshot = dict[str, dict[str, str]]

with open(_ROOT / "ethernaut.json") as f:
    _eth = json.load(f)
    LEVEL_FACTORIES = [
        Address(int.from_bytes(bytes.fromhex(_eth[str(i)][2:]))) for i in range(COUNT)
    ]

cache: Snapshot | None = None


def snapshot_contracts(address: Address) -> Blockchain:
    """Load the given contract from the snapshot, and any contracts it references."""
    global cache
    if cache is None:
        with open(_ROOT / "snapshot.json") as f:
            cache = json.load(f)
        assert cache is not None
    raw = cache[address.to_bytes(20).hex()]

    blockchain = Blockchain()
    contract = Contract(
        program=disassemble(Bytes.fromhex(raw["code"])),
        # Some level factories create other contracts in their constructor. To
        # avoid address collisions between these fixed contracts and created
        # level contracts, bump up the nonce.
        nonce=16,
    )
    for k, v in raw.items():
        if k == "code":
            continue
        vx = int(v, 16)
        contract.storage[Uint256(int(k))] = Uint256(vx)
        if is_sibling_contract(vx, slot=int(k)):
            # Warning! Levels like Delegation include global non-factory
            # contracts that *do* need to be interacted with.
            blockchain.contracts.update(snapshot_contracts(vx).contracts)

    blockchain.contracts[address] = contract
    return blockchain


def get_code(address: Address) -> Program:
    """Load the Contract at a given address."""
    data = _api_request("eth_getCode", address=address.to_bytes(20).hex(), tag=TAG)
    return disassemble(Bytes(data))


def get_storage_at(address: Address, position: int) -> Uint256:
    """Load the contents of a given storage slot."""
    value = _api_request(
        "eth_getStorageAt",
        address=address.to_bytes(20).hex(),
        position=position.to_bytes(32).hex(),
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


def download_contract(snapshot: Snapshot, address: Address) -> None:
    """Download a given address's code and data."""
    program = get_code(address)
    key = address.to_bytes(20).hex()
    assert (c := program.code.reveal()) is not None
    snapshot[key] = {"code": c.hex()}

    for j in range(8):
        # HACK: level factories only use the first few storage slots. Higher
        # slots are for maps keyed by player, which we can initialize to zero.
        storage = get_storage_at(address, j)
        assert (v := storage.reveal()) is not None
        if v != 0:
            snapshot[key][str(j)] = v.to_bytes(32).hex()
        if is_sibling_contract(j, slot=v):
            download_contract(snapshot, j)


def is_sibling_contract(value: int, *, slot: int) -> TypeGuard[Address]:
    """Check if a given storage slot refers to a related contract."""
    # According to the `Level` interface, the contract's owner is stored in slot
    # zero. Don't try to download that contract.
    return slot > 0 and value > 2**156 and value < 2**160
