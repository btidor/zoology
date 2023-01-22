#!/usr/bin/env pytest

import copy
from typing import Any, Callable, Protocol, TypeVar

import pytest

from arrays import FrozenBytes
from disassembler import Program, disassemble
from sha3 import SHA3
from symbolic import BA, BW, unwrap, unwrap_bytes, zstore
from testlib import (
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


class Benchmark(Protocol):
    T = TypeVar("T")

    def __call__(self, fn: Callable[..., T], *args: Any) -> T:
        ...


@pytest.fixture
def fallback() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Fallback {

            mapping(address => uint) public contributions;
            address public owner;

            constructor() {
                owner = msg.sender;
                contributions[msg.sender] = 1000 * (1 ether);
            }

            modifier onlyOwner {
                require(
                    msg.sender == owner,
                    "caller is not the owner"
                );
                _;
            }

            function contribute() public payable {
                require(msg.value < 0.001 ether);
                contributions[msg.sender] += msg.value;
                if(contributions[msg.sender] > contributions[owner]) {
                    owner = msg.sender;
                }
            }

            function getContribution() public view returns (uint) {
                return contributions[msg.sender];
            }

            function withdraw() public onlyOwner {
                payable(owner).transfer(address(this).balance);
            }

            receive() external payable {
                require(msg.value > 0 && contributions[msg.sender] > 0);
                owner = msg.sender;
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_fallback(benchmark: Benchmark, fallback: Program) -> None:
    state = make_state(
        contract=make_contract(program=fallback),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("owner()")),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(0))


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


@pytest.fixture
def fallout() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Fallout {
            mapping(address => uint) allocations;
            address payable public owner;

            /* constructor */
            function Fal1out() public payable {
                owner = payable(msg.sender);
                allocations[owner] = msg.value;
            }

            modifier onlyOwner {
                require(
                    msg.sender == owner,
                    "caller is not the owner"
                );
                _;
            }

            function allocate() public payable {
                allocations[msg.sender] += msg.value;
            }

            function sendAllocation(address payable allocator) public {
                require(allocations[allocator] > 0);
                allocator.transfer(allocations[allocator]);
            }

            function collectAllocations() public onlyOwner {
                payable(msg.sender).transfer(address(this).balance);
            }

            function allocatorBalance(address allocator) public view returns(uint) {
                return allocations[allocator];
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_fallout(benchmark: Benchmark, fallout: Program) -> None:
    state = make_state(
        contract=make_contract(program=fallout),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(abiencode("Fal1out()")),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(
        BW(0xCACACACACACACACACACACACACACACACACACACACA)
    )


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


@pytest.fixture
def coinflip() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract CoinFlip {

            uint256 public consecutiveWins;
            uint256 lastHash;
            uint256 FACTOR = 57896044618658097711785492504343953926634992332820282019728792003956564819968;

            constructor() {
                consecutiveWins = 0;
            }

            function flip(bool _guess) public returns (bool) {
                uint256 blockValue = uint256(blockhash(block.number - 1));

                if (lastHash == blockValue) {
                    revert();
                }

                lastHash = blockValue;
                uint256 coinFlip = blockValue / FACTOR;
                bool side = coinFlip == 1 ? true : false;

                if (side == _guess) {
                    consecutiveWins++;
                    return true;
                } else {
                    consecutiveWins = 0;
                    return false;
                }
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_coinflip(benchmark: Benchmark, coinflip: Program) -> None:
    state = make_state(
        contract=make_contract(program=coinflip),
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

    benchmark(execute, state)
    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(BW(0))


def test_explore_coinflip(benchmark: Benchmark, coinflip: Program) -> None:
    benchmark(check_paths, coinflip, set(["Px19", "Px6FD", "Px6FF", "PxDF9", "PxDFD"]))


def test_analyze_coinflip(coinflip: Program) -> None:
    universal = universal_transaction(coinflip, SHA3(), "")
    check_transition(*next(universal), 0x6FF, "SAVE", "flip(bool)")
    check_transition(*next(universal), 0xDFD, "SAVE", "flip(bool)")
    # TODO: there are more???


@pytest.fixture
def telephone() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Telephone {

            address public owner;

            constructor() {
                owner = msg.sender;
            }

            function changeOwner(address _owner) public {
                if (tx.origin != msg.sender) {
                    owner = _owner;
                }
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_telephone(benchmark: Benchmark, telephone: Program) -> None:
    state = make_state(
        contract=make_contract(program=telephone),
        transaction=make_transaction(
            caller=BA(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("changeOwner(address)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
            ),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_telephone(benchmark: Benchmark, telephone: Program) -> None:
    benchmark(check_paths, telephone, set(["PxD", "PxCF", "PxCE"]))


def test_analyze_telephone(telephone: Program) -> None:
    universal = universal_transaction(telephone, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "owner()")
    check_transition(*next(universal), 0xCF, "VIEW", "changeOwner(address)")
    check_transition(*next(universal), 0xCE, "SAVE", "changeOwner(address)")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.fixture
def token() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.6.0;

        contract Token {

            mapping(address => uint) balances;
            uint public totalSupply;

            constructor(uint _initialSupply) public {
                balances[msg.sender] = totalSupply = _initialSupply;
            }

            function transfer(address _to, uint _value) public returns (bool) {
                require(balances[msg.sender] - _value >= 0);
                balances[msg.sender] -= _value;
                balances[_to] += _value;
                return true;
            }

            function balanceOf(address _owner) public view returns (uint balance) {
                return balances[_owner];
            }
        }
    """
    code = compile_solidity(source, version=Solidity.v06)
    return disassemble(code)


def test_execute_token(benchmark: Benchmark, token: Program) -> None:
    state = make_state(
        contract=make_contract(program=token),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("transfer(address,uint256)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                + unwrap_bytes(BW(0xEEEE))
            ),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))


def test_explore_token(benchmark: Benchmark, token: Program) -> None:
    benchmark(check_paths, token, set(["PxD", "Px33", "PxC7"]))


def test_analyze_token(token: Program) -> None:
    universal = universal_transaction(token, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "totalSupply()")
    check_transition(*next(universal), 0x33, "VIEW", "balanceOf(address)")
    check_transition(*next(universal), 0xC7, "SAVE", "transfer(address,uint256)")

    with pytest.raises(StopIteration):
        next(universal)


delegation_source = """
    // SPDX-License-Identifier: MIT
    pragma solidity ^0.8.0;

    contract Delegate {

        address public owner;

        constructor(address _owner) {
            owner = _owner;
        }

        function pwn() public {
            owner = msg.sender;
        }
    }

    contract Delegation {

        address public owner;
        Delegate delegate;

        constructor(address _delegateAddress) {
            delegate = Delegate(_delegateAddress);
            owner = msg.sender;
        }

        fallback() external {
            (bool result,) = address(delegate).delegatecall(msg.data);
            if (result) {
                this;
            }
        }
    }
"""


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


@pytest.fixture
def vault() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Vault {
            bool public locked;
            bytes32 private password;

            constructor(bytes32 _password) {
                locked = true;
                password = _password;
            }

            function unlock(bytes32 _password) public {
                if (password == _password) {
                    locked = false;
                }
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_vault(benchmark: Benchmark, vault: Program) -> None:
    state = make_state(
        contract=make_contract(program=vault),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=FrozenBytes.concrete(
                abiencode("unlock(bytes32)") + unwrap_bytes(BW(0))
            ),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


def test_explore_vault(benchmark: Benchmark, vault: Program) -> None:
    benchmark(check_paths, vault, set(["PxD", "PxCF", "PxCE"]))


def test_analyze_value(vault: Program) -> None:
    universal = universal_transaction(vault, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "locked()")
    check_transition(*next(universal), 0xCF, "VIEW", "unlock(bytes32)")
    check_transition(*next(universal), 0xCE, "SAVE", "unlock(bytes32)")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.fixture
def king() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract King {

            address king;
            uint public prize;
            address public owner;

            constructor() payable {
                owner = msg.sender;
                king = msg.sender;
                prize = msg.value;
            }

            receive() external payable {
                require(msg.value >= prize || msg.sender == owner);
                payable(king).transfer(msg.value);
                king = msg.sender;
                prize = msg.value;
            }

            function _king() public view returns (address) {
                return king;
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_king(benchmark: Benchmark, king: Program) -> None:
    state = make_state(
        contract=make_contract(program=king),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


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


@pytest.fixture
def reentrancy() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Reentrance {

            mapping(address => uint) public balances;

            function donate(address _to) public payable {
                balances[_to] += msg.value;
            }

            function balanceOf(address _who) public view returns (uint balance) {
                return balances[_who];
            }

            function withdraw(uint _amount) public {
                if(balances[msg.sender] >= _amount) {
                    (bool result,) = msg.sender.call{value:_amount}("");
                    if(result) {
                        _amount;
                    }
                    balances[msg.sender] -= _amount;
                }
            }

            receive() external payable {}
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_reentrancy(benchmark: Benchmark, reentrancy: Program) -> None:
    state = make_state(
        contract=make_contract(program=reentrancy),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=FrozenBytes.concrete(
                abiencode("donate(address)") + unwrap_bytes(BW(1))
            ),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


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


elevator_source = """
    // SPDX-License-Identifier: MIT
    pragma solidity ^0.8.0;

    interface Building {
        function isLastFloor(uint) external returns (bool);
    }

    contract Elevator {
        bool public top;
        uint public floor;

        function goTo(uint _floor) public {
            Building building = Building(msg.sender);

            if (! building.isLastFloor(_floor)) {
                floor = _floor;
                top = building.isLastFloor(floor);
            }
        }
    }

    contract TestBuilding is Building {
        function isLastFloor(uint floor) external pure returns (bool) {
            return floor == 12;
        }
    }
"""


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


@pytest.fixture
def gatekeeper_one() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract GatekeeperOne {

            address public entrant;

            modifier gateOne() {
                require(msg.sender != tx.origin);
                _;
            }

            modifier gateTwo() {
                require(gasleft() % 8191 == 0);
                _;
            }

            modifier gateThree(bytes8 _gateKey) {
                require(uint32(uint64(_gateKey)) == uint16(uint64(_gateKey)), "GatekeeperOne: invalid gateThree part one");
                require(uint32(uint64(_gateKey)) != uint64(_gateKey), "GatekeeperOne: invalid gateThree part two");
                require(uint32(uint64(_gateKey)) == uint16(uint160(tx.origin)), "GatekeeperOne: invalid gateThree part three");
                _;
            }

            function enter(bytes8 _gateKey) public gateOne gateTwo gateThree(_gateKey) returns (bool) {
                entrant = tx.origin;
                return true;
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


# Gatekeeper One: we can't test execute() because concrete gas is not
# implemented.


def test_explore_gatekeeper_one(benchmark: Benchmark, gatekeeper_one: Program) -> None:
    benchmark(check_paths, gatekeeper_one, set(["PxDFF", "Px19"]))


def test_analyze_gatekeeper_one(gatekeeper_one: Program) -> None:
    universal = universal_transaction(gatekeeper_one, SHA3(), "")
    check_transition(*next(universal), 0xDFF, "SAVE", "enter(bytes8)")
    check_transition(*next(universal), 0x19, "VIEW", "entrant()")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.fixture
def gatekeeper_two() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract GatekeeperTwo {

            address public entrant;

            modifier gateOne() {
                require(msg.sender != tx.origin);
                _;
            }

            modifier gateTwo() {
                uint x;
                assembly { x := extcodesize(caller()) }
                require(x == 0);
                _;
            }

            modifier gateThree(bytes8 _gateKey) {
                require(uint64(bytes8(keccak256(abi.encodePacked(msg.sender)))) ^ uint64(_gateKey) == type(uint64).max);
                _;
            }

            function enter(bytes8 _gateKey) public gateOne gateTwo gateThree(_gateKey) returns (bool) {
                entrant = tx.origin;
                return true;
            }
        }
    """
    code = compile_solidity(source)
    return disassemble(code)


def test_execute_gatekeeper_two(benchmark: Benchmark, gatekeeper_two: Program) -> None:
    state = make_state(
        contract=make_contract(program=gatekeeper_two),
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

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))


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


preservation_source = """
    // SPDX-License-Identifier: MIT
    pragma solidity ^0.8.0;

    contract Preservation {

        // public library contracts
        address public timeZone1Library;
        address public timeZone2Library;
        address public owner;
        uint storedTime;
        // Sets the function signature for delegatecall
        bytes4 constant setTimeSignature = bytes4(keccak256("setTime(uint256)"));

        constructor(address _timeZone1LibraryAddress, address _timeZone2LibraryAddress) {
            timeZone1Library = _timeZone1LibraryAddress;
            timeZone2Library = _timeZone2LibraryAddress;
            owner = msg.sender;
        }

        // set the time for timezone 1
        function setFirstTime(uint _timeStamp) public {
            timeZone1Library.delegatecall(abi.encodePacked(setTimeSignature, _timeStamp));
        }

        // set the time for timezone 2
        function setSecondTime(uint _timeStamp) public {
            timeZone2Library.delegatecall(abi.encodePacked(setTimeSignature, _timeStamp));
        }
    }

    // Simple library contract to set the time
    contract LibraryContract {

        // stores a timestamp
        uint storedTime;

        function setTime(uint _time) public {
            storedTime = _time;
        }
    }
"""


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


@pytest.fixture
def recovery() -> Program:
    source = """
        // SPDX-License-Identifier: MIT
        pragma solidity ^0.8.0;

        contract Recovery {

            //generate tokens
            function generateToken(string memory _name, uint256 _initialSupply) public {
                new SimpleToken(_name, msg.sender, _initialSupply);

            }
        }

        contract SimpleToken {

            string public name;
            mapping (address => uint) public balances;

            // constructor
            constructor(string memory _name, address _creator, uint256 _initialSupply) {
                name = _name;
                balances[_creator] = _initialSupply;
            }

            // collect ether in return for tokens
            receive() external payable {
                balances[msg.sender] = msg.value * 10;
            }

            // allow transfers of tokens
            function transfer(address _to, uint _amount) public {
                require(balances[msg.sender] >= _amount);
                balances[msg.sender] = balances[msg.sender] - _amount;
                balances[_to] = _amount;
            }

            // clean up after ourselves
            function destroy(address payable _to) public {
                selfdestruct(_to);
            }
        }
    """
    return disassemble(compile_solidity(source, "SimpleToken"))


def test_execute_recovery(benchmark: Benchmark, recovery: Program) -> None:
    state = make_state(
        contract=make_contract(program=recovery),
        transaction=make_transaction(
            callvalue=BW(0x1000),
            calldata=FrozenBytes.concrete(b""),
        ),
    )

    benchmark(execute, state)

    assert state.success is True
    assert state.returndata.require_concrete() == b""


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
