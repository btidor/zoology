import os
import subprocess
from enum import Enum
from typing import Dict, List, Literal, Optional, assert_never

import z3
from Crypto.Hash import keccak

from disassembler import Program, disassemble
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from state import State
from symbolic import (
    BA,
    BW,
    Array,
    Bytes,
    Constraint,
    check,
    solver_stack,
    uint8,
    uint160,
    uint256,
)
from universal import constrain_to_goal
from vm import concrete_DELEGATECALL, concrete_GAS, concrete_JUMPI, step


class Solidity(Enum):
    v08 = "0.8.17"
    v06 = "0.6.12"


def make_block(
    number: Optional[uint256] = None,
    coinbase: Optional[uint256] = None,
    timestamp: Optional[uint256] = None,
    prevrandao: Optional[uint256] = None,
    gaslimit: Optional[uint256] = None,
    chainid: Optional[uint256] = None,
    basefee: Optional[uint256] = None,
) -> Block:
    return Block(
        number=BW(16030969) if number is None else number,
        coinbase=BA(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5)
        if coinbase is None
        else coinbase,
        timestamp=BW(1669214471) if timestamp is None else timestamp,
        prevrandao=BW(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        )
        if prevrandao is None
        else prevrandao,
        gaslimit=BW(30000000000000000) if gaslimit is None else gaslimit,
        chainid=BW(1) if chainid is None else chainid,
        basefee=BW(12267131109) if basefee is None else basefee,
    )


def make_contract(
    address: Optional[uint160] = None,
    program: Optional[Program] = None,
    storage: Optional[Array] = None,
) -> Contract:
    return Contract(
        address=BA(0xADADADADADADADADADADADADADADADADADADADAD)
        if address is None
        else address,
        program=disassemble(b"") if program is None else program,
        storage=Array("STORAGE", z3.BitVecSort(256), BW(0))
        if storage is None
        else storage,
    )


def make_transaction(
    origin: Optional[uint160] = None,
    caller: Optional[uint160] = None,
    callvalue: Optional[uint256] = None,
    calldata: Optional[Bytes] = None,
    gasprice: Optional[uint256] = None,
) -> Transaction:
    return Transaction(
        origin=BA(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
        if origin is None
        else origin,
        caller=BA(0xCACACACACACACACACACACACACACACACACACACACA)
        if caller is None
        else caller,
        callvalue=BW(0) if callvalue is None else callvalue,
        calldata=Bytes.concrete(b"") if calldata is None else calldata,
        gasprice=BW(0x12) if gasprice is None else gasprice,
    )


def make_universe(
    suffix: Optional[str] = None,
    balances: Optional[Array] = None,
    transfer_constraints: Optional[List[Constraint]] = None,
    contracts: Optional[Dict[int, Contract]] = None,
    blockhashes: Optional[Array] = None,
    agents: Optional[List[uint160]] = None,
    contribution: Optional[uint256] = None,
    extraction: Optional[uint256] = None,
) -> Universe:
    return Universe(
        suffix="" if suffix is None else suffix,
        balances=Array("BALANCE", z3.BitVecSort(160), BW(0))
        if balances is None
        else balances,
        transfer_constraints=[]
        if transfer_constraints is None
        else transfer_constraints,
        contracts={} if contracts is None else contracts,
        blockhashes=Array("BLOCKHASH", z3.BitVecSort(256), BW(0))
        if blockhashes is None
        else blockhashes,
        agents=[] if agents is None else agents,
        contribution=BW(0) if contribution is None else contribution,
        extraction=BW(0) if extraction is None else extraction,
    )


def make_state(
    suffix: Optional[str] = None,
    block: Optional[Block] = None,
    contract: Optional[Contract] = None,
    transaction: Optional[Transaction] = None,
    universe: Optional[Universe] = None,
    sha3: Optional[SHA3] = None,
    pc: Optional[int] = None,
    stack: Optional[List[uint256]] = None,
    memory: Optional[Dict[int, uint8]] = None,
    returndata: Optional[Bytes] = None,
    success: Optional[bool] = None,
    subcontexts: Optional[List[State]] = None,
    gas_variables: Optional[List[uint256]] = None,
    path_constraints: Optional[List[Constraint]] = None,
    path: Optional[int] = None,
) -> State:
    return State(
        suffix="" if suffix is None else suffix,
        block=make_block() if block is None else block,
        contract=make_contract() if contract is None else contract,
        transaction=make_transaction() if transaction is None else transaction,
        universe=make_universe() if universe is None else universe,
        sha3=SHA3() if sha3 is None else sha3,
        pc=0 if pc is None else pc,
        stack=[] if stack is None else stack,
        memory={} if memory is None else memory,
        returndata=Bytes.concrete(b"") if returndata is None else returndata,
        success=None if success is None else success,
        subcontexts=[] if subcontexts is None else subcontexts,
        gas_variables=[] if gas_variables is None else gas_variables,
        path_constraints=[] if path_constraints is None else path_constraints,
        path=1 if path is None else path,
    )


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
        elif action == "GAS":
            concrete_GAS(state)
        elif action == "DELEGATECALL":
            with concrete_DELEGATECALL(state) as substate:
                execute(substate)
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
