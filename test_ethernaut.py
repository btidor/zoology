#!/usr/bin/env pytest

import pytest

from disassembler import disassemble
from sha3 import SHA3
from symbolic import BW, Bytes, unwrap_bytes
from testlib import (
    abiencode,
    check_transition,
    compile_solidity,
    execute,
    make_contract,
    make_state,
    make_transaction,
)
from universal import printable_transition, universal_transaction


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
    code = compile_solidity(source, "0.8.17")
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
    assert state.returndata.require_concrete() == b"\x00" * 32

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
    code = compile_solidity(source, "0.8.17")
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
    print()
    assert unwrap_bytes(state.contract.storage[BW(1)]) == (b"\x00" * 12 + b"\xca" * 20)

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
