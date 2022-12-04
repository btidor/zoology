#!/usr/bin/env pytest

import pytest

from disassembler import disassemble
from sha3 import SHA3
from symbolic import BA, BW, Bytes, unwrap_bytes
from testlib import (
    Solidity,
    abiencode,
    check_transition,
    compile_solidity,
    execute,
    make_contract,
    make_state,
    make_transaction,
)
from universal import printable_transition, universal_transaction
from vm import printable_execution


def test_fallback() -> None:
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
    code = compile_solidity(source, Solidity.v08)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes("CALLDATA", abiencode("owner()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(0))

    universal = universal_transaction(program, SHA3(), "")

    start, end = next(universal)
    check_transition(start, end, 0x19, "SAVE", None, 1)

    start, end = next(universal)
    check_transition(start, end, 0x2F, "GOAL", "withdraw()")

    start, end = next(universal)
    check_transition(start, end, 0x4F, "VIEW", "contributions(address)")

    start, end = next(universal)
    check_transition(start, end, 0x23, "VIEW", "owner()")

    start, end = next(universal)
    check_transition(start, end, 0x10F, "SAVE", "contribute()")

    start, end = next(universal)
    check_transition(start, end, 0x10E, "SAVE", "contribute()")

    start, end = next(universal)
    check_transition(start, end, 0x83, "VIEW", "getContribution()")

    with pytest.raises(StopIteration):
        next(universal)


def test_fallout() -> None:
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
    code = compile_solidity(source, Solidity.v08)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes("CALLDATA", abiencode("Fal1out()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(
        BW(0xCACACACACACACACACACACACACACACACACACACACA)
    )

    universal = universal_transaction(program, SHA3(), "")

    start, end = next(universal)
    check_transition(start, end, 0x5, "SAVE", "Fal1out()")

    start, end = next(universal)
    check_transition(start, end, 0x4F, "GOAL", "collectAllocations()")

    start, end = next(universal)
    check_transition(start, end, 0x23, "VIEW", "owner()")

    start, end = next(universal)
    check_transition(start, end, 0x43F, "GOAL", "sendAllocation(address)")

    start, end = next(universal)
    check_transition(start, end, 0x83, "SAVE", "allocate()")

    start, end = next(universal)
    check_transition(start, end, 0x40F, "VIEW", "allocatorBalance(address)")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.mark.skip("implement BLOCKHASH")
def test_coinflip() -> None:
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
    code = compile_solidity(source, Solidity.v08)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes("CALLDATA", abiencode("flip(bool)") + unwrap_bytes(BW(0))),
        ),
    )
    execute(state)
    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(BW(0))

    assert False  # finish test


@pytest.mark.skip("implement OWNER != CALLER")
def test_telephone() -> None:
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
    code = compile_solidity(source, Solidity.v08)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            caller=BA(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=BW(0),
            calldata=Bytes(
                "CALLDATA",
                abiencode("changeOwner(address)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)),
            ),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")

    start, end = next(universal)
    check_transition(start, end, 0xD, "VIEW", "owner()")

    start, end = next(universal)
    check_transition(start, end, 0xCF, "GOAL", "changeOwner(address)")

    with pytest.raises(StopIteration):
        next(universal)


def test_token() -> None:
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
    code = compile_solidity(source, Solidity.v06)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes(
                "CALLDATA",
                abiencode("transfer(address,uint256)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                + unwrap_bytes(BW(0xEEEE)),
            ),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))

    universal = universal_transaction(program, SHA3(), "")

    start, end = next(universal)
    check_transition(start, end, 0xD, "VIEW", "totalSupply()")

    start, end = next(universal)
    check_transition(start, end, 0x33, "VIEW", "balanceOf(address)")

    start, end = next(universal)
    check_transition(start, end, 0xC7, "SAVE", "transfer(address,uint256)")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.mark.skip("implement GAS")
def test_delegation() -> None:
    source = """
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
    code = compile_solidity(source, Solidity.v08, "Delegation")
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes("CALLDATA", abiencode("pwn()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")

    start, end = next(universal)
    check_transition(start, end, 0x0, "VIEW", "owner()")

    start, end = next(universal)
    check_transition(start, end, 0x0, "SAVE", "pwn()")

    with pytest.raises(StopIteration):
        next(universal)

    assert False
