#!/usr/bin/env pytest

import copy
from typing import Any, Callable, Protocol, TypeVar

import pytest

from arrays import FrozenBytes
from disassembler import Program, disassemble
from sha3 import SHA3
from symbolic import BA, BW, unwrap, unwrap_bytes, zstore
from testlib import (
    Benchmark,
    Solidity,
    abiencode,
    check_paths,
    check_transition,
    compile_solidity,
    execute,
    make_contract,
    make_state,
    make_transaction,
)
from universal import _universal_transaction, symbolic_start, universal_transaction

# TODO: separate timings for `narrow()` step


def test_explore_fallback(benchmark: Benchmark, fallback: Program) -> None:
    benchmark(
        check_paths,
        fallback,
        set(["Px19", "Px2F", "Px4F", "Px23", "Px10F", "Px10E", "Px83"]),
    )


def test_analyze_fallback(fallback: Program) -> None:
    universal = universal_transaction(fallback, SHA3(), "")
    check_transition(*next(universal), 0x19, "SAVE", None, 1)
    check_transition(*next(universal), 0x2F, "GOAL", "withdraw()")
    check_transition(*next(universal), 0x4F, "VIEW", "contributions(address)")
    check_transition(*next(universal), 0x23, "VIEW", "owner()")
    check_transition(*next(universal), 0x10F, "SAVE", "contribute()")
    check_transition(*next(universal), 0x10E, "SAVE", "contribute()")
    check_transition(*next(universal), 0x83, "VIEW", "getContribution()")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_fallout(benchmark: Benchmark, fallout: Program) -> None:
    benchmark(
        check_paths, fallout, set(["Px5", "Px4F", "Px23", "Px43F", "Px83", "Px40F"])
    )


def test_analyze_fallout(fallout: Program) -> None:
    universal = universal_transaction(fallout, SHA3(), "")
    check_transition(*next(universal), 0x5, "SAVE", "Fal1out()")
    check_transition(*next(universal), 0x4F, "GOAL", "collectAllocations()")
    check_transition(*next(universal), 0x23, "VIEW", "owner()")
    check_transition(*next(universal), 0x43F, "GOAL", "sendAllocation(address)")
    check_transition(*next(universal), 0x83, "SAVE", "allocate()")
    check_transition(*next(universal), 0x40F, "VIEW", "allocatorBalance(address)")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_coinflip(benchmark: Benchmark, coinflip: Program) -> None:
    benchmark(check_paths, coinflip, set(["Px19", "Px6FD", "Px6FF", "PxDF9", "PxDFD"]))


def test_analyze_coinflip(coinflip: Program) -> None:
    universal = universal_transaction(coinflip, SHA3(), "")
    check_transition(*next(universal), 0x6FF, "SAVE", "flip(bool)")
    check_transition(*next(universal), 0xDFD, "SAVE", "flip(bool)")
    # TODO: there are more???


def test_explore_telephone(benchmark: Benchmark, telephone: Program) -> None:
    benchmark(check_paths, telephone, set(["PxD", "PxCF", "PxCE"]))


def test_analyze_telephone(telephone: Program) -> None:
    universal = universal_transaction(telephone, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "owner()")
    check_transition(*next(universal), 0xCF, "VIEW", "changeOwner(address)")
    check_transition(*next(universal), 0xCE, "SAVE", "changeOwner(address)")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_token(benchmark: Benchmark, token: Program) -> None:
    benchmark(check_paths, token, set(["PxD", "Px33", "PxC7"]))


def test_analyze_token(token: Program) -> None:
    universal = universal_transaction(token, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "totalSupply()")
    check_transition(*next(universal), 0x33, "VIEW", "balanceOf(address)")
    check_transition(*next(universal), 0xC7, "SAVE", "transfer(address,uint256)")

    with pytest.raises(StopIteration):
        next(universal)


def test_execute_delegation(benchmark: Benchmark) -> None:
    delegate = disassemble(compile_solidity(delegation_source, contract="Delegate"))
    delegation = disassemble(compile_solidity(delegation_source, contract="Delegation"))

    other = make_contract(address=BA(0xABCDEF), program=delegate)
    state = make_state(
        contract=make_contract(program=delegation),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("pwn()")),
        ),
    )
    state.universe.add_contract(other)
    state.contract.storage.array = zstore(
        state.contract.storage.array, BW(1), BW(unwrap(other.address))
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_delegation(benchmark: Benchmark) -> None:
    delegate = disassemble(compile_solidity(delegation_source, contract="Delegate"))
    delegation = disassemble(compile_solidity(delegation_source, contract="Delegation"))

    other = make_contract(address=BA(0xABCDEF), program=delegate)
    start = symbolic_start(delegation, SHA3(), "")
    init = copy.deepcopy(start)
    init.universe.transfer(
        init.transaction.caller, init.contract.address, init.transaction.callvalue
    )
    init.universe.add_contract(other)
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(1), BW(unwrap(other.address))
    )

    benchmark(check_paths, init, set(["PxF", "PxD", "PxC9", "Px19"]))


def test_analyze_delegation() -> None:
    delegate = disassemble(compile_solidity(delegation_source, contract="Delegate"))
    delegation = disassemble(compile_solidity(delegation_source, contract="Delegation"))

    other = make_contract(address=BA(0xABCDEF), program=delegate)
    start = symbolic_start(delegation, SHA3(), "")
    init = copy.deepcopy(start)
    init.universe.transfer(
        init.transaction.caller, init.contract.address, init.transaction.callvalue
    )
    init.universe.add_contract(other)
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(1), BW(unwrap(other.address))
    )

    universal = _universal_transaction(init)
    check_transition(start, next(universal), 0xF, "VIEW", None)  # *
    check_transition(start, next(universal), 0xD, "VIEW", "owner()")
    check_transition(start, next(universal), 0xC9, "SAVE", "pwn()")
    check_transition(start, next(universal), 0x19, "VIEW", "$any4")  # *
    # * if Delegate reverts, Delegation will still return successfully

    with pytest.raises(StopIteration):
        next(universal)


@pytest.fixture
def force() -> Program:
    code = bytes.fromhex(
        "6080604052600080fdfea26469706673582212203717ccea65e207051915ebdbec707aead0330450f3d14318591e16cc74fd06bc64736f6c634300080c0033"
    )
    return disassemble(code)


def test_execute_force(benchmark: Benchmark, force: Program) -> None:
    state = make_state(
        contract=make_contract(program=force),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    benchmark(execute, state)

    assert state.success is False
    assert state.returndata.require_concrete() == b""


def test_explore_force(force: Program) -> None:
    check_paths(force, set())


def test_explore_vault(benchmark: Benchmark, vault: Program) -> None:
    benchmark(check_paths, vault, set(["PxD", "PxCF", "PxCE"]))


def test_analyze_value(vault: Program) -> None:
    universal = universal_transaction(vault, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "locked()")
    check_transition(*next(universal), 0xCF, "VIEW", "unlock(bytes32)")
    check_transition(*next(universal), 0xCE, "SAVE", "unlock(bytes32)")

    with pytest.raises(StopIteration):
        next(universal)


# @pytest.mark.skip("slow?") TODO
def test_explore_king(benchmark: Benchmark, king: Program) -> None:
    benchmark(check_paths, king, set(["Px37", "Px33", "PxB", "Px13", "Px23"]))


@pytest.mark.skip("slow")
def test_analyze_king(king: Program) -> None:
    universal = universal_transaction(king, SHA3(), "")
    check_transition(*next(universal), 0x37, "SAVE", None, None)
    check_transition(*next(universal), 0x33, "SAVE", None, None)
    check_transition(*next(universal), 0xB, "VIEW", "_king()")
    check_transition(*next(universal), 0x13, "VIEW", "owner()")
    check_transition(*next(universal), 0x23, "VIEW", "prize()")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_reentrancy(benchmark: Benchmark, reentrancy: Program) -> None:
    benchmark(
        check_paths,
        reentrancy,
        set(["Px6", "Px2F", "Px4F", "Px11F", "Px47B", "Px479", "Px10F"]),
    )


def test_analyze_reentrancy(reentrancy: Program) -> None:
    universal = universal_transaction(reentrancy, SHA3(), "")
    check_transition(*next(universal), 0x6, "VIEW", None)
    check_transition(*next(universal), 0x2F, "SAVE", "donate(address)")
    check_transition(*next(universal), 0x4F, "VIEW", "balances(address)")
    check_transition(*next(universal), 0x11F, "VIEW", "withdraw(uint256)")
    check_transition(*next(universal), 0x47B, "GOAL", "withdraw(uint256)")
    check_transition(*next(universal), 0x479, "GOAL", "withdraw(uint256)")
    check_transition(*next(universal), 0x10F, "VIEW", "balanceOf(address)")

    with pytest.raises(StopIteration):
        next(universal)


def test_execute_elevator(benchmark: Benchmark) -> None:
    elevator = disassemble(compile_solidity(elevator_source, "Elevator"))
    building = disassemble(compile_solidity(elevator_source, "TestBuilding"))

    state = make_state(
        contract=make_contract(program=elevator),
        transaction=make_transaction(
            caller=BA(0x76543210),
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("goTo(uint256)") + unwrap_bytes(BW(1))
            ),
        ),
    )
    state.universe.add_contract(make_contract(address=BA(0x76543210), program=building))

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_elevator(benchmark: Benchmark) -> None:
    elevator = disassemble(compile_solidity(elevator_source, "Elevator"))

    benchmark(check_paths, elevator, set(["PxD", "Px67F", "Px33F7", "Px31"]))


def test_analyze_elevator() -> None:
    elevator = disassemble(compile_solidity(elevator_source, "Elevator"))

    universal = universal_transaction(elevator, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "floor()")
    check_transition(*next(universal), 0x67F, "VIEW", "goTo(uint256)")
    check_transition(*next(universal), 0x33F7, "SAVE", "goTo(uint256)")
    check_transition(*next(universal), 0x31, "VIEW", "top()")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.fixture
def privacy() -> Program:
    code = bytes.fromhex(
        "6080604052348015600f57600080fd5b5060043610603c5760003560e01c8063b3cea217146041578063cf30901214605c578063e1afb08c146077575b600080fd5b604960015481565b6040519081526020015b60405180910390f35b60005460689060ff1681565b60405190151581526020016053565b6086608236600460b8565b6088565b005b6005546fffffffffffffffffffffffffffffffff1982811691161460ab57600080fd5b506000805460ff19169055565b60006020828403121560c957600080fd5b81356fffffffffffffffffffffffffffffffff198116811460e957600080fd5b939250505056fea2646970667358221220199fe33db58ed15b2bbeab277974ecd5658987f1e54e16ba5130d3be0834910e64736f6c634300080c0033"
    )
    return disassemble(code)


def test_execute_privacy(benchmark: Benchmark, privacy: Program) -> None:
    state = make_state(
        contract=make_contract(program=privacy),
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

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_privacy(privacy: Program) -> None:
    check_paths(privacy, set(["PxD", "Px19", "Px18F"]))


def test_analyze_privacy(privacy: Program) -> None:
    universal = universal_transaction(privacy, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "ID()")
    check_transition(*next(universal), 0x19, "VIEW", "locked()")
    check_transition(*next(universal), 0x18F, "SAVE", "unlock(bytes16)")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_gatekeeper_one(benchmark: Benchmark, gatekeeper_one: Program) -> None:
    benchmark(check_paths, gatekeeper_one, set(["PxDFF", "Px19"]))


def test_analyze_gatekeeper_one(gatekeeper_one: Program) -> None:
    universal = universal_transaction(gatekeeper_one, SHA3(), "")
    check_transition(*next(universal), 0xDFF, "SAVE", "enter(bytes8)")
    check_transition(*next(universal), 0x19, "VIEW", "entrant()")

    with pytest.raises(StopIteration):
        next(universal)


def test_explore_gatekeeper_two(benchmark: Benchmark, gatekeeper_two: Program) -> None:
    benchmark(check_paths, gatekeeper_two, set(["Px1BF", "Px19"]))


def test_analyze_gatekeeper_two(gatekeeper_two: Program) -> None:
    universal = universal_transaction(gatekeeper_two, SHA3(), "")
    check_transition(*next(universal), 0x1BF, "SAVE", "enter(bytes8)")
    check_transition(*next(universal), 0x19, "VIEW", "entrant()")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.mark.skip("TODO")
def test_naughtcoin() -> None:
    raise NotImplementedError("openzeppelin erc-20")


def test_execute_preservation(benchmark: Benchmark) -> None:
    preservation = make_contract(
        program=disassemble(compile_solidity(preservation_source, "Preservation"))
    )
    library = make_contract(
        address=BA(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=disassemble(compile_solidity(preservation_source, "LibraryContract")),
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

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_preservation(benchmark: Benchmark) -> None:
    preservation = make_contract(
        program=disassemble(compile_solidity(preservation_source, "Preservation"))
    )
    library = make_contract(
        address=BA(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=disassemble(compile_solidity(preservation_source, "LibraryContract")),
    )
    start = symbolic_start(preservation.program, SHA3(), "")
    init = copy.deepcopy(start)
    init.universe.transfer(
        init.transaction.caller, init.contract.address, init.transaction.callvalue
    )
    init.universe.add_contract(library)
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(0), BW(unwrap(library.address))
    )
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(1), BW(unwrap(library.address))
    )

    benchmark(
        check_paths,
        init,
        set(["PxD", "Px19", "PxC737", "PxC73", "Px61", "Px30737", "Px3073"]),
    )


def test_analyze_preservation() -> None:
    preservation = make_contract(
        program=disassemble(compile_solidity(preservation_source, "Preservation"))
    )
    library = make_contract(
        address=BA(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=disassemble(compile_solidity(preservation_source, "LibraryContract")),
    )
    start = symbolic_start(preservation.program, SHA3(), "")
    init = copy.deepcopy(start)
    init.universe.transfer(
        init.transaction.caller, init.contract.address, init.transaction.callvalue
    )
    init.universe.add_contract(library)
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(0), BW(unwrap(library.address))
    )
    init.contract.storage.array = zstore(
        init.contract.storage.array, BW(1), BW(unwrap(library.address))
    )

    universal = _universal_transaction(init)
    check_transition(start, next(universal), 0xD, "VIEW", "timeZone2Library()")
    check_transition(start, next(universal), 0x19, "VIEW", "timeZone1Library()")
    check_transition(start, next(universal), 0xC737, "SAVE", "setTime(uint256)")
    # TODO: should be SAVE
    check_transition(start, next(universal), 0xC73, "VIEW", "setSecondTime(uint256)")
    check_transition(start, next(universal), 0x61, "VIEW", "owner()")
    check_transition(start, next(universal), 0x30737, "SAVE", "setTime(uint256)")
    # TODO: should be SAVE
    check_transition(start, next(universal), 0x3073, "VIEW", "setFirstTime(uint256)")

    with pytest.raises(StopIteration):
        next(universal)



@pytest.mark.skip("SELFDESTRUCT not implemented")
def test_explore_recovery(benchmark: Benchmark, recovery: Program) -> None:
    benchmark(check_paths, recovery, set(["PxD"]))


def test_analyze_recovery(recovery: Program) -> None:
    universal = universal_transaction(recovery, SHA3(), "")
    check_transition(*next(universal), 0xD, "SAVE", None)

    with pytest.raises(NotImplementedError):  # DELEGATECALL
        next(universal)

    # TODO: some branches are missing because of the error

    with pytest.raises(StopIteration):
        next(universal)
