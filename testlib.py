import os
import subprocess
from typing import Any, Dict

import z3
from Crypto.Hash import keccak

from disassembler import Program
from environment import Block, Contract, Universe
from sha3 import SHA3
from state import State
from symbolic import BA, BW, Array, Bytes


def make_block(**kwargs: Any) -> Block:
    attrs: Dict[str, Any] = {
        "number": BW(16030969),
        "coinbase": BA(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5),
        "timestamp": BW(1669214471),
        "prevrandao": BW(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        ),
        "gaslimit": BW(30000000000000000),
        "chainid": BW(1),
        "basefee": BW(12267131109),
    }
    attrs.update(**kwargs)
    return Block(**attrs)


def make_contract(**kwargs: Any) -> Contract:
    attrs: Dict[str, Any] = {
        "program": Program(),
        "storage": Array("STORAGE", z3.BitVecSort(256), BW(0)),
    }
    attrs.update(**kwargs)
    return Contract(**attrs)


def make_universe(**kwargs: Any) -> Universe:
    attrs: Dict[str, Any] = {
        "suffix": "",
        "balances": Array("BALANCE", z3.BitVecSort(160), BW(0)),
        "transfer_constraints": [],
        "agents": [],
        "contribution": BW(0),
        "extraction": BW(0),
    }
    attrs.update(**kwargs)
    return Universe(**attrs)


def make_state(**kwargs: Any) -> State:
    attrs: Dict[str, Any] = {
        "suffix": "",
        "block": make_block(),
        "contract": make_contract(),
        "universe": make_universe(),
        "sha3": SHA3(),
        "pc": 0,
        "stack": [],
        "memory": {},
        "address": BA(0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA),
        "origin": BA(0xBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB),
        "caller": BA(0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC),
        "callvalue": BW(0),
        "calldata": Bytes("", b""),
        "gasprice": BW(0x12),
        "returndata": Bytes("", b""),
        "success": None,
        "path_constraints": [],
        "path": 1,
    }
    attrs.update(**kwargs)
    return State(**attrs)


def compile_solidity(source: str, version: str) -> bytes:
    env = os.environ.copy()
    env["SOLC_VERSION"] = version
    output = subprocess.check_output(
        ["solc", "--bin-runtime", "-"], env=env, input=source.encode()
    )
    hexstr = output.splitlines()[-2].decode()
    return bytes.fromhex(hexstr)


def abiencode(signature: str) -> bytes:
    return keccak.new(data=signature.encode(), digest_bits=256).digest()[:4]
