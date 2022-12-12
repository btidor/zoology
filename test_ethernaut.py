#!/usr/bin/env pytest

import pytest

from disassembler import disassemble
from sha3 import SHA3
from symbolic import BA, BW, Bytes, unwrap, unwrap_bytes
from testlib import (
    Solidity,
    abiencode,
    check_transition,
    compile_solidity,
    execute,
    make_contract,
    make_state,
    make_transaction,
    make_universe,
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
    code = compile_solidity(source)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(abiencode("owner()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(0))

    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0x19, "SAVE", None, 1)
    check_transition(*next(universal), 0x2F, "GOAL", "withdraw()")
    check_transition(*next(universal), 0x4F, "VIEW", "contributions(address)")
    check_transition(*next(universal), 0x23, "VIEW", "owner()")
    check_transition(*next(universal), 0x10F, "SAVE", "contribute()")
    check_transition(*next(universal), 0x10E, "SAVE", "contribute()")
    check_transition(*next(universal), 0x83, "VIEW", "getContribution()")

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
    code = compile_solidity(source)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(abiencode("Fal1out()")),
        ),
    )
    execute(state)
    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(
        BW(0xCACACACACACACACACACACACACACACACACACACACA)
    )

    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0x5, "SAVE", "Fal1out()")
    check_transition(*next(universal), 0x4F, "GOAL", "collectAllocations()")
    check_transition(*next(universal), 0x23, "VIEW", "owner()")
    check_transition(*next(universal), 0x43F, "GOAL", "sendAllocation(address)")
    check_transition(*next(universal), 0x83, "SAVE", "allocate()")
    check_transition(*next(universal), 0x40F, "VIEW", "allocatorBalance(address)")

    with pytest.raises(StopIteration):
        next(universal)


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
    code = compile_solidity(source)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(abiencode("flip(bool)") + unwrap_bytes(BW(0))),
        ),
    )
    state.contract.storage[BW(1)] = BW(0xFEDC)
    state.contract.storage[BW(2)] = BW(
        57896044618658097711785492504343953926634992332820282019728792003956564819968
    )
    execute(state)
    assert state.success is True
    assert unwrap_bytes(state.contract.storage[BW(1)]) == unwrap_bytes(BW(0))

    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0x6FF, "SAVE", "flip(bool)")
    check_transition(*next(universal), 0xDFD, "SAVE", "flip(bool)")


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
    code = compile_solidity(source)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            caller=BA(0xB1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1),
            callvalue=BW(0),
            calldata=Bytes.concrete(
                abiencode("changeOwner(address)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
            ),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "owner()")
    check_transition(*next(universal), 0xCF, "VIEW", "changeOwner(address)")
    check_transition(*next(universal), 0xCE, "SAVE", "changeOwner(address)")

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
    code = compile_solidity(source, version=Solidity.v06)
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(
                abiencode("transfer(address,uint256)")
                + unwrap_bytes(BW(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF))
                + unwrap_bytes(BW(0xEEEE))
            ),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == unwrap_bytes(BW(1))

    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0xD, "VIEW", "totalSupply()")
    check_transition(*next(universal), 0x33, "VIEW", "balanceOf(address)")
    check_transition(*next(universal), 0xC7, "SAVE", "transfer(address,uint256)")

    with pytest.raises(StopIteration):
        next(universal)


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
    delegate = disassemble(compile_solidity(source, contract="Delegate"))
    delegation = disassemble(compile_solidity(source, contract="Delegation"))

    other = make_contract(address=BA(0xABCDEF), program=delegate)
    state = make_state(
        contract=make_contract(program=delegation),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(abiencode("pwn()")),
        ),
        universe=make_universe(contracts={unwrap(other.address): other}),
    )
    state.contract.storage[BW(1)] = BW(unwrap(other.address))
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    # TODO: implement byte-array copy with symbolic arguments

    # universal = universal_transaction(delegation, SHA3(), "")
    # check_transition(*next(universal), 0x0, "VIEW", "owner()")
    # check_transition(*next(universal), 0x0, "SAVE", "pwn()")

    # with pytest.raises(StopIteration):
    #     next(universal)


def test_force() -> None:
    code = bytes.fromhex(
        "6080604052600080fdfea26469706673582212203717ccea65e207051915ebdbec707aead0330450f3d14318591e16cc74fd06bc64736f6c634300080c0033"
    )
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=Bytes.concrete(b""),
        ),
    )
    execute(state)
    assert state.success is False
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")

    with pytest.raises(StopIteration):
        next(universal)


def test_vault() -> None:
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
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0),
            calldata=Bytes.concrete(abiencode("unlock(bytes32)") + unwrap_bytes(BW(0))),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")

    check_transition(*next(universal), 0xD, "VIEW", "locked()")
    check_transition(*next(universal), 0xCF, "VIEW", "unlock(bytes32)")
    check_transition(*next(universal), 0xCE, "SAVE", "unlock(bytes32)")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.mark.skip("slow")
def test_king() -> None:
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
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=Bytes.concrete(b""),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    universal = universal_transaction(program, SHA3(), "")

    check_transition(*next(universal), 0x37, "SAVE", None, None)
    check_transition(*next(universal), 0x33, "SAVE", None, None)
    check_transition(*next(universal), 0xB, "VIEW", "_king()")
    check_transition(*next(universal), 0x13, "VIEW", "owner()")
    check_transition(*next(universal), 0x23, "VIEW", "prize()")

    with pytest.raises(StopIteration):
        next(universal)


@pytest.mark.skip("implement CALL properly")
def test_reentrancy() -> None:
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
    program = disassemble(code)

    state = make_state(
        contract=make_contract(program=program),
        transaction=make_transaction(
            callvalue=BW(0x1234),
            calldata=Bytes.concrete(abiencode("donate(address)") + unwrap_bytes(BW(1))),
        ),
    )
    execute(state)
    assert state.success is True
    assert state.returndata.require_concrete() == b""

    assert False
