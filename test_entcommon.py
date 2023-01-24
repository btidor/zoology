from typing import Dict

from disassembler import Program
from sha3 import SHA3
from state import State
from symbolic import BA, BW, unwrap, zstore
from testlib import make_contract
from universal import symbolic_start

Fallback = (
    ("Px19", "SAVE", None, 1),
    ("Px2F", "GOAL", "withdraw()"),
    ("Px4F", "VIEW", "contributions(address)"),
    ("Px23", "VIEW", "owner()"),
    ("Px10F", "SAVE", "contribute()"),
    ("Px10E", "SAVE", "contribute()"),
    ("Px83", "VIEW", "getContribution()"),
)

Fallout = (
    ("Px5", "SAVE", "Fal1out()"),
    ("Px4F", "GOAL", "collectAllocations()"),
    ("Px23", "VIEW", "owner()"),
    ("Px43F", "GOAL", "sendAllocation(address)"),
    ("Px83", "SAVE", "allocate()"),
    ("Px40F", "VIEW", "allocatorBalance(address)"),
)

CoinFlip = (
    ("Px6FF", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px6FD", "TODO", ""),
    ("PxDF9", "TODO", ""),
    ("PxDFD", "TODO", ""),
    ("Px19", "TODO", ""),
)

Telephone = (
    ("PxD", "VIEW", "owner()"),
    ("PxCF", "VIEW", "changeOwner(address)"),
    ("PxCE", "SAVE", "changeOwner(address)"),
)

Token = (
    ("PxD", "VIEW", "totalSupply()"),
    ("Px33", "VIEW", "balanceOf(address)"),
    ("PxC7", "SAVE", "transfer(address,uint256)"),
)

Delegation = (
    ("PxF", "VIEW", None),  # *
    ("PxD", "VIEW", "owner()"),
    ("PxC9", "SAVE", "pwn()"),
    ("Px19", "VIEW", "$any4"),  # *
    # * if Delegate reverts, Delegation will still return successfully
)

Force = ()

Vault = (
    ("PxD", "VIEW", "locked()"),
    ("PxCF", "VIEW", "unlock(bytes32)"),
    ("PxCE", "SAVE", "unlock(bytes32)"),
)

King = (
    ("Px37", "SAVE", None, None),
    ("Px33", "SAVE", None, None),
    ("PxB", "VIEW", "_king()"),
    ("Px13", "VIEW", "owner()"),
    ("Px23", "VIEW", "prize()"),
)

Reentrancy = (
    ("Px6", "VIEW", None),
    ("Px2F", "SAVE", "donate(address)"),
    ("Px4F", "VIEW", "balances(address)"),
    ("Px11F", "VIEW", "withdraw(uint256)"),
    ("Px47B", "GOAL", "withdraw(uint256)"),
    ("Px479", "GOAL", "withdraw(uint256)"),
    ("Px10F", "VIEW", "balanceOf(address)"),
)

Elevator = (
    ("PxD", "VIEW", "floor()"),
    ("Px67F", "VIEW", "goTo(uint256)"),
    ("Px33F7", "SAVE", "goTo(uint256)"),
    ("Px31", "VIEW", "top()"),
)

Privacy = (
    ("PxD", "VIEW", "ID()"),
    ("Px19", "VIEW", "locked()"),
    ("Px18F", "SAVE", "unlock(bytes16)"),
)

GatekeeperOne = (
    ("PxDFF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

GatekeeperTwo = (
    ("Px1BF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

Preservation = (
    ("PxD", "VIEW", "timeZone2Library()"),
    ("Px19", "VIEW", "timeZone1Library()"),
    ("PxC737", "SAVE", "setTime(uint256)"),
    ("PxC73", "VIEW", "setSecondTime(uint256)"),  # TODO: should be SAVE
    ("Px61", "VIEW", "owner()"),
    ("Px30737", "SAVE", "setTime(uint256)"),
    ("Px3073", "VIEW", "setFirstTime(uint256)"),  # TODO: should be SAVE
)


def delegation_start(programs: Dict[str, Program]) -> State:
    other = make_contract(address=BA(0xABCDEF), program=programs["Delegate"])
    start = symbolic_start(programs["Delegation"], SHA3(), "")
    start.universe.transfer(
        start.transaction.caller, start.contract.address, start.transaction.callvalue
    )
    start.universe.add_contract(other)
    start.contract.storage.array = zstore(
        start.contract.storage.array, BW(1), BW(unwrap(other.address))
    )
    return start


def preservation_start(programs: Dict[str, Program]) -> State:
    preservation = make_contract(program=programs["Preservation"])
    library = make_contract(
        address=BA(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    start = symbolic_start(preservation.program, SHA3(), "")
    start.universe.transfer(
        start.transaction.caller, start.contract.address, start.transaction.callvalue
    )
    start.universe.add_contract(library)
    start.contract.storage.array = zstore(
        start.contract.storage.array, BW(0), BW(unwrap(library.address))
    )
    start.contract.storage.array = zstore(
        start.contract.storage.array, BW(1), BW(unwrap(library.address))
    )
    return start
