#!/usr/bin/env pytest

import copy

from arrays import FrozenBytes
from state import State
from symbolic import BA, BW, unwrap, unwrap_bytes, zstore
from testlib import (
    Benchmark,
    abiencode,
    execute,
    load_binary,
    load_solidity,
    loads_solidity,
    make_contract,
    make_state,
    make_transaction,
)


def bench(benchmark: Benchmark, state: State) -> State:
    return benchmark.pedantic(
        execute,
        setup=lambda: ((copy.deepcopy(state),), {}),
        rounds=20,
    )


def test_fallback(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/01_Fallback.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(0))


def test_fallout(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/02_Fallout.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("Fal1out()")),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(
        BW(0xCACACACACACACACACACACACACACACACACACACACA)
    )


def test_coinflip(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/03_CoinFlip.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("flip(bool)") + unwrap_bytes(BW(0))
            ),
        ),
    )
    state.contract.storage[BW(1)] = BW(0xFEDC)
    state.contract.storage[BW(2)] = BW(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(BW(0))


def test_telephone(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/04_Telephone.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            caller=BA(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("changeOwner(address)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_token(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/05_Token.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("transfer(address,uint256)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                + unwrap_bytes(BW(0xEEEE))
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))


def test_delegation(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/06_Delegation.sol")

    other = make_contract(address=BA(0xABCDEF), program=programs["Delegate"])
    state = make_state(
        contract=make_contract(program=programs["Delegation"]),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("pwn()")),
        ),
    )
    state.universe.add_contract(other)
    state.contract.storage.array = zstore(
        state.contract.storage.array, BW(1), BW(unwrap(other.address))
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_force(benchmark: Benchmark) -> None:
    program = load_binary("ethernaut/07_Force.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is False
    assert state.returndata.require_concrete() == b""


def test_vault(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/08_Vault.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes32)") + unwrap_bytes(BW(0))
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_king(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/09_King.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_reentrancy(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/10_Reentrancy.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(
                abiencode("donate(address)") + unwrap_bytes(BW(1))
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_elevator(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/11_Elevator.sol")

    state = make_state(
        contract=make_contract(program=programs["Elevator"]),
        transaction=make_transaction(
            caller=BA(0x76543210),
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("goTo(uint256)") + unwrap_bytes(BW(1))
            ),
        ),
    )
    state.universe.add_contract(
        make_contract(address=BA(0x76543210), program=programs["TestBuilding"])
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_privacy(benchmark: Benchmark) -> None:
    program = load_binary("ethernaut/12_Privacy.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes16)") + unwrap_bytes(BW(0x4321 << 128))
            ),
        ),
    )
    state.contract.storage.array = zstore(
        state.contract.storage.array, BW(5), BW(0x4321 << 128)
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_gatekeeper_one(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/13_GatekeeperOne.sol")
    # TODO: we can't test GatekeeperOne because concrete gas isn't implemented


def test_gatekeeper_two(benchmark: Benchmark) -> None:
    program = load_solidity("ethernaut/14_GatekeeperTwo.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("enter(bytes8)")
                + bytes.fromhex(
                    "65d5bd2c953ab27b000000000000000000000000000000000000000000000000"
                )
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))


def test_preservation(benchmark: Benchmark) -> None:
    programs = loads_solidity("ethernaut/15_Preservation.sol")
    preservation = make_contract(program=programs["Preservation"])
    library = make_contract(
        address=BA(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    state = make_state(
        contract=preservation,
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("setFirstTime(uint256)") + unwrap_bytes(BW(0x5050))
            ),
        ),
    )
    state.universe.add_contract(library)
    state.contract.storage.array = zstore(
        state.contract.storage.array, BW(0), BW(unwrap(library.address))
    )
    state.contract.storage.array = zstore(
        state.contract.storage.array, BW(1), BW(unwrap(library.address))
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""
