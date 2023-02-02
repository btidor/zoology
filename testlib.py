from typing import Any, Dict, List, Literal, Optional, Tuple, Union, assert_never

from arrays import Array, FrozenBytes, MutableBytes
from disassembler import Program, disassemble
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from smt import BitVector, Constraint, Uint160, Uint256
from solidity import abiencode
from solver import Solver
from state import State
from universal import _universal_transaction, constrain_to_goal, symbolic_start
from vm import (
    concrete_CALLCODE,
    concrete_DELEGATECALL,
    concrete_GAS,
    concrete_JUMPI,
    concrete_STATICCALL,
    hybrid_CALL,
    step,
)


def concretize(value: Optional[BitVector]) -> Optional[int]:
    if value is None:
        return None
    return value.unwrap()


def make_block(
    number: Optional[Uint256] = None,
    coinbase: Optional[Uint160] = None,
    timestamp: Optional[Uint256] = None,
    prevrandao: Optional[Uint256] = None,
    gaslimit: Optional[Uint256] = None,
    chainid: Optional[Uint256] = None,
    basefee: Optional[Uint256] = None,
) -> Block:
    return Block(
        number=Uint256(16030969) if number is None else number,
        coinbase=Uint160(0xDAFEA492D9C6733AE3D56B7ED1ADB60692C98BC5)
        if coinbase is None
        else coinbase,
        timestamp=Uint256(1669214471) if timestamp is None else timestamp,
        prevrandao=Uint256(
            0xCC7E0A66B3B9E3F54B7FDB9DCF98D57C03226D73BFFBB4E0BA7B08F92CE00D19
        )
        if prevrandao is None
        else prevrandao,
        gaslimit=Uint256(30000000000000000) if gaslimit is None else gaslimit,
        chainid=Uint256(1) if chainid is None else chainid,
        basefee=Uint256(12267131109) if basefee is None else basefee,
    )


def make_contract(
    address: Optional[Uint160] = None,
    program: Optional[Program] = None,
    storage: Optional[Array[Uint256, Uint256]] = None,
) -> Contract:
    return Contract(
        address=Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
        if address is None
        else address,
        program=disassemble(b"") if program is None else program,
        storage=Array.concrete(Uint256, Uint256(0)) if storage is None else storage,
    )


def make_transaction(
    origin: Optional[Uint160] = None,
    caller: Optional[Uint160] = None,
    callvalue: Optional[Uint256] = None,
    calldata: Optional[FrozenBytes] = None,
    gasprice: Optional[Uint256] = None,
) -> Transaction:
    return Transaction(
        origin=Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)
        if origin is None
        else origin,
        caller=Uint160(0xCACACACACACACACACACACACACACACACACACACACA)
        if caller is None
        else caller,
        callvalue=Uint256(0) if callvalue is None else callvalue,
        calldata=FrozenBytes.concrete(b"") if calldata is None else calldata,
        gasprice=Uint256(0x12) if gasprice is None else gasprice,
    )


def make_universe(
    suffix: Optional[str] = None,
    balances: Optional[Array[Uint160, Uint256]] = None,
    transfer_constraints: Optional[List[Constraint]] = None,
    contracts: Optional[Dict[int, Contract]] = None,
    codesizes: Optional[Array[Uint160, Uint256]] = None,
    blockhashes: Optional[Array[Uint256, Uint256]] = None,
    agents: Optional[List[Uint160]] = None,
    contribution: Optional[Uint256] = None,
    extraction: Optional[Uint256] = None,
) -> Universe:
    return Universe(
        suffix="" if suffix is None else suffix,
        balances=Array.concrete(Uint160, Uint256(0)) if balances is None else balances,
        transfer_constraints=[]
        if transfer_constraints is None
        else transfer_constraints,
        contracts={} if contracts is None else contracts,
        codesizes=Array.concrete(Uint160, Uint256(0))
        if codesizes is None
        else codesizes,
        blockhashes=Array.concrete(Uint256, Uint256(0))
        if blockhashes is None
        else blockhashes,
        agents=[] if agents is None else agents,
        contribution=Uint256(0) if contribution is None else contribution,
        extraction=Uint256(0) if extraction is None else extraction,
    )


def make_state(
    suffix: Optional[str] = None,
    block: Optional[Block] = None,
    contract: Optional[Contract] = None,
    transaction: Optional[Transaction] = None,
    universe: Optional[Universe] = None,
    sha3: Optional[SHA3] = None,
    pc: Optional[int] = None,
    stack: Optional[List[Uint256]] = None,
    memory: Optional[MutableBytes] = None,
    returndata: Optional[FrozenBytes] = None,
    success: Optional[bool] = None,
    subcontexts: Optional[List[State]] = None,
    gas_variables: Optional[List[Uint256]] = None,
    call_variables: Optional[List[Tuple[FrozenBytes, Constraint]]] = None,
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
        memory=MutableBytes.concrete(b"") if memory is None else memory,
        returndata=FrozenBytes.concrete(b"") if returndata is None else returndata,
        success=None if success is None else success,
        subcontexts=[] if subcontexts is None else subcontexts,
        gas_variables=[] if gas_variables is None else gas_variables,
        call_variables=[] if call_variables is None else call_variables,
        path_constraints=[] if path_constraints is None else path_constraints,
        path=1 if path is None else path,
    )


def execute(state: State) -> State:
    while True:
        action = step(state)
        if action == "CONTINUE":
            continue
        elif action == "JUMPI":
            concrete_JUMPI(state)
        elif action == "GAS":
            concrete_GAS(state)
        elif action == "CALL":
            for substate in hybrid_CALL(state):
                execute(substate)
        elif action == "CALLCODE":
            with concrete_CALLCODE(state) as substate:
                execute(substate)
        elif action == "DELEGATECALL":
            with concrete_DELEGATECALL(state) as substate:
                execute(substate)
        elif action == "STATICCALL":
            with concrete_STATICCALL(state) as substate:
                execute(substate)
        elif action == "TERMINATE":
            return state
        else:
            assert_never(action)


def check_paths(input: Union[Program, State], branches: Tuple[Any, ...]) -> None:
    expected = set(b[0] for b in branches)
    if isinstance(input, Program):
        input = symbolic_start(input, SHA3(), "")
    actual = set()
    for end in _universal_transaction(input):
        assert end.px() not in actual, "duplicate path"
        actual.add(end.px())
    assert actual == expected


def check_transition(
    start: State,
    end: State,
    path: int,
    kind: Literal["GOAL", "SAVE", "VIEW"],
    method: Optional[str],
    value: Optional[int] = None,
) -> None:
    assert end.path == path, f"unexpected path: {end.px()}"
    assert end.success is True

    solver = Solver()
    end.constrain(solver)
    constrain_to_goal(solver, start, end)
    assert solver.check() == (kind == "GOAL")

    if kind != "GOAL":
        assert end.is_changed(start) == (kind == "SAVE")

    solver = Solver()
    end.constrain(solver)
    assert solver.check()

    end.narrow(solver)
    transaction = end.transaction.evaluate(solver)

    actual = bytes.fromhex(transaction.get("Data", "")[2:10])
    if method is None:
        assert actual == b"", f"unexpected data: {actual.hex()}"
    elif method.startswith("0x"):
        assert actual == bytes.fromhex(method[2:]), f"unexpected data: {actual.hex()}"
    elif method == "$any4":
        assert len(actual) == 4, f"unexpected data: {actual.hex()}"
    else:
        assert actual == abiencode(method), f"unexpected data: {actual.hex()}"

    if "Value" not in transaction:
        assert value is None
    else:
        assert value is not None
        assert transaction["Value"] == "0x" + int.to_bytes(value, 32).hex()
