from typing import Literal

from arrays import Array, FrozenBytes, MutableBytes
from disassembler import Program, disassemble
from environment import Block, Contract, Transaction, Universe
from sha3 import SHA3
from smt import BitVector, Constraint, Uint160, Uint256
from solidity import abiencode
from solver import Solver
from state import Log, State, Termination
from universal import constrain_to_goal
from vm import printable_execution


def concretize(value: BitVector | None) -> int | None:
    if value is None:
        return None
    return value.unwrap()


def make_block(
    number: Uint256 | None = None,
    coinbase: Uint160 | None = None,
    timestamp: Uint256 | None = None,
    prevrandao: Uint256 | None = None,
    gaslimit: Uint256 | None = None,
    chainid: Uint256 | None = None,
    basefee: Uint256 | None = None,
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
    address: Uint160 | None = None,
    program: Program | None = None,
    storage: Array[Uint256, Uint256] | None = None,
) -> Contract:
    return Contract(
        address=Uint160(0xADADADADADADADADADADADADADADADADADADADAD)
        if address is None
        else address,
        program=disassemble(b"") if program is None else program,
        storage=Array.concrete(Uint256, Uint256(0)) if storage is None else storage,
    )


def make_transaction(
    origin: Uint160 | None = None,
    caller: Uint160 | None = None,
    callvalue: Uint256 | None = None,
    calldata: FrozenBytes | None = None,
    gasprice: Uint256 | None = None,
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
    suffix: str | None = None,
    balances: Array[Uint160, Uint256] | None = None,
    transfer_constraints: list[Constraint] | None = None,
    contracts: dict[int, Contract] | None = None,
    codesizes: Array[Uint160, Uint256] | None = None,
    blockhashes: Array[Uint256, Uint256] | None = None,
    agents: list[Uint160] | None = None,
    contribution: Uint256 | None = None,
    extraction: Uint256 | None = None,
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
    suffix: str | None = None,
    block: Block | None = None,
    contract: Contract | None = None,
    transaction: Transaction | None = None,
    universe: Universe | None = None,
    sha3: SHA3 | None = None,
    pc: int | None = None,
    stack: list[Uint256] | None = None,
    memory: MutableBytes | None = None,
    children: int | None = None,
    latest_return: FrozenBytes | None = None,
    logs: list[Log] | None = None,
    gas_variables: list[Uint256] | None = None,
    call_variables: list[tuple[FrozenBytes, Constraint]] | None = None,
    path_constraints: list[Constraint] | None = None,
    path: int | None = None,
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
        children=0 if children is None else children,
        latest_return=FrozenBytes.concrete(b"")
        if latest_return is None
        else latest_return,
        logs=[] if logs is None else logs,
        gas_variables=gas_variables,
        call_variables=[] if call_variables is None else call_variables,
        path_constraints=[] if path_constraints is None else path_constraints,
        path=1 if path is None else path,
    )


def execute(state: State) -> State:
    generator = printable_execution(state)
    try:
        while True:
            next(generator)
    except StopIteration as e:
        assert isinstance(e.value, State)
        return e.value


def check_transition(
    start: State,
    end: State,
    path: int,
    kind: Literal["GOAL", "SAVE", "VIEW"],
    method: str | None,
    value: int | None = None,
) -> None:
    assert end.path == path, f"unexpected path: {end.px()}"
    assert isinstance(end.pc, Termination)
    assert end.pc.success is True

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
    transaction = end.transaction.describe(solver)

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
