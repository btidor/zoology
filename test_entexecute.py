#!/usr/bin/env pytest

import copy

from arrays import FrozenBytes
from smt import Uint160, Uint256
from state import State
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
from vm import printable_execution


def bench(benchmark: Benchmark, state: State) -> State:
    return benchmark.pedantic(
        execute,
        setup=lambda: ((copy.deepcopy(state),), {}),
        rounds=20,
    )


def test_fallback(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/01_Fallback.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == Uint256(0).unwrap(bytes)


def test_fallout(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/02_Fallout.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("Fal1out()")),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.contract.storage[Uint256(1)].unwrap(bytes) == Uint256(
        0xCACACACACACACACACACACACACACACACACACACACA
    ).unwrap(bytes)


def test_coinflip(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/03_CoinFlip.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("flip(bool)") + Uint256(0).unwrap(bytes)
            ),
        ),
    )
    state.contract.storage[Uint256(1)] = Uint256(0xFEDC)
    state.contract.storage[Uint256(2)] = Uint256(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.contract.storage[Uint256(1)].unwrap(bytes) == Uint256(0).unwrap(bytes)


def test_telephone(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/04_Telephone.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            caller=Uint160(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("changeOwner(address)")
                + Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).unwrap(bytes)
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_token(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/05_Token.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("transfer(address,uint256)")
                + Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF).unwrap(bytes)
                + Uint256(0xEEEE).unwrap(bytes)
            ),
        ),
    )

    # state = bench(benchmark, state)

    for line in printable_execution(state):
        print(line)

    assert state.success is True
    assert state.returndata.unwrap() == Uint256(1).unwrap(bytes)


def test_delegation(benchmark: Benchmark) -> None:
    programs = loads_solidity("fixtures/06_Delegation.sol")

    other = make_contract(address=Uint160(0xABCDEF), program=programs["Delegate"])
    state = make_state(
        contract=make_contract(program=programs["Delegation"]),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(abiencode("pwn()")),
        ),
    )
    state.universe.add_contract(other)
    state.contract.storage.poke(Uint256(1), other.address.into(Uint256))

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_force(benchmark: Benchmark) -> None:
    program = load_binary("fixtures/07_Force.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is False
    assert state.returndata.unwrap() == b""


def test_vault(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/08_Vault.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes32)") + Uint256(0).unwrap(bytes)
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_king(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/09_King.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_reentrancy(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/10_Reentrancy.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0x1234),
            calldata=FrozenBytes.concrete(
                abiencode("donate(address)") + Uint256(1).unwrap(bytes)
            ),
        ),
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_elevator(benchmark: Benchmark) -> None:
    programs = loads_solidity("fixtures/11_Elevator.sol")

    state = make_state(
        contract=make_contract(program=programs["Elevator"]),
        transaction=make_transaction(
            caller=Uint160(0x76543210),
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("goTo(uint256)") + Uint256(1).unwrap(bytes)
            ),
        ),
    )
    state.universe.add_contract(
        make_contract(address=Uint160(0x76543210), program=programs["TestBuilding"])
    )

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_privacy(benchmark: Benchmark) -> None:
    program = load_binary("fixtures/12_Privacy.bin")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes16)") + Uint256(0x4321 << 128).unwrap(bytes)
            ),
        ),
    )
    state.contract.storage.poke(Uint256(5), Uint256(0x4321 << 128))

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""


def test_gatekeeper_one(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/13_GatekeeperOne.sol")
    # TODO: we can't test GatekeeperOne because concrete gas isn't implemented


def test_gatekeeper_two(benchmark: Benchmark) -> None:
    program = load_solidity("fixtures/14_GatekeeperTwo.sol")
    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=Uint256(0),
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
    assert state.returndata.unwrap() == Uint256(1).unwrap(bytes)


def test_preservation(benchmark: Benchmark) -> None:
    programs = loads_solidity("fixtures/15_Preservation.sol")
    preservation = make_contract(program=programs["Preservation"])
    library = make_contract(
        address=Uint160(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    state = make_state(
        contract=preservation,
        transaction=make_transaction(
            callvalue=Uint256(0),
            calldata=FrozenBytes.concrete(
                abiencode("setFirstTime(uint256)") + Uint256(0x5050).unwrap(bytes)
            ),
        ),
    )
    state.universe.add_contract(library)
    state.contract.storage.poke(Uint256(0), library.address.into(Uint256))
    state.contract.storage.poke(Uint256(1), library.address.into(Uint256))

    state = bench(benchmark, state)

    assert state.success is True
    assert state.returndata.unwrap() == b""
