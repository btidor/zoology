import os
import subprocess
from enum import Enum
from typing import Any, Dict, Literal, Optional, assert_never

import z3
from Crypto.Hash import keccak

from disassembler import Program
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from state import State
from symbolic import BA, BW, Array, Bytes, check, solver_stack
from universal import constrain_to_goal
from vm import concrete_JUMPI, step


class Solidity(Enum):
    v08 = "0.8.17"
    v06 = "0.6.12"


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
        "address": BA(0xADADADADADADADADADADADADADADADADADADADAD),
        "program": Program(),
        "storage": Array("STORAGE", z3.BitVecSort(256), BW(0)),
    }
    attrs.update(**kwargs)
    return Contract(**attrs)


def make_transaction(**kwargs: Any) -> Transaction:
    attrs: Dict[str, Any] = {
        "origin": BA(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0),
        "caller": BA(0xCACACACACACACACACACACACACACACACACACACACA),
        "callvalue": BW(0),
        "calldata": Bytes("", b""),
        "gasprice": BW(0x12),
    }
    attrs.update(**kwargs)
    return Transaction(**attrs)


def make_universe(**kwargs: Any) -> Universe:
    attrs: Dict[str, Any] = {
        "suffix": "",
        "balances": Array("BALANCE", z3.BitVecSort(160), BW(0)),
        "transfer_constraints": [],
        "blockhashes": Array("BLOCKHASH", z3.BitVecSort(256), BW(0)),
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
        "transaction": make_transaction(),
        "universe": make_universe(),
        "sha3": SHA3(),
        "pc": 0,
        "stack": [],
        "memory": {},
        "returndata": Bytes("", b""),
        "success": None,
        "path_constraints": [],
        "path": 1,
    }
    attrs.update(**kwargs)
    return State(**attrs)


def compile_solidity(
    source: str,
    contract: Optional[str] = None,
    version: Solidity = Solidity.v08,
) -> bytes:
    env = os.environ.copy()
    env["SOLC_VERSION"] = version.value
    output = subprocess.check_output(
        ["solc", "--bin-runtime", "-"], env=env, input=source.encode()
    ).splitlines()

    current = "<unknown>"
    matches: Dict[str, bytes] = {}
    for i in range(len(output)):
        if output[i].startswith(b"======="):
            current = output[i].split(b" ")[1][8:].decode()
        if output[i] == b"Binary of the runtime part:":
            matches[current] = bytes.fromhex(output[i + 1].decode())

    if contract is None:
        assert len(matches) == 1
        return list(matches.values())[0]
    else:
        return matches[contract]


def install_solidity() -> None:
    marker = os.path.expanduser("~/.config/solc-versions")
    target = [version.value for version in Solidity]
    if os.path.exists(marker):
        with open(marker) as f:
            if f.read() == str(target):
                return

    for version in Solidity:
        subprocess.check_call(["solc-select", "install", version.value])

    with open(marker, "w") as f:
        f.write(str(target))


def abiencode(signature: str) -> bytes:
    return keccak.new(data=signature.encode(), digest_bits=256).digest()[:4]


def execute(state: State) -> None:
    while True:
        action = step(state)
        if action == "CONTINUE":
            continue
        elif action == "JUMPI":
            concrete_JUMPI(state)
        elif action == "TERMINATE":
            return
        else:
            assert_never(action)


def check_transition(
    start: State,
    end: State,
    path: int,
    kind: Literal["GOAL", "SAVE", "VIEW"],
    method: Optional[str],
    value: Optional[int] = None,
) -> None:
    assert end.path == path
    assert end.success is True

    solver = z3.Optimize()
    end.constrain(solver, minimize=True)
    with solver_stack(solver):
        constrain_to_goal(solver, start, end)
        assert check(solver) == (kind == "GOAL")

    if kind != "GOAL":
        assert end.is_changed(solver, start) == (kind == "SAVE")
    assert check(solver)

    model = end.narrow(solver, solver.model())
    transaction = end.transaction.evaluate(model)

    actual = bytes.fromhex(transaction.get("Data", "")[2:10])
    if method is None:
        assert actual == b""
    elif method.startswith("0x"):
        assert actual == bytes.fromhex(method[2:])
    else:
        assert actual == abiencode(method)

    if "Value" not in transaction:
        assert value is None
    else:
        assert value is not None
        assert transaction["Value"] == "0x" + int.to_bytes(value, 32).hex()
