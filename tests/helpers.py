"""Test helpers, mostly related to fixtures."""

from disassembler import Program
from environment import Contract
from sha3 import SHA3
from smt import Uint160, Uint256
from state import State
from universal import symbolic_start

type Branch = tuple[str, str, str | None] | tuple[str, str, str | None, int | None]
type Branches = tuple[Branch, ...]

Fallback: Branches = (
    ("Px19", "SAVE", None, 1),
    ("PxB9", "SAVE", "withdraw()"),
    ("Px23", "VIEW", "owner()"),
    ("Px5F", "SAVE", "withdraw()"),
    ("Px4F", "VIEW", "contributions(address)"),
    ("Px83", "VIEW", "getContribution()"),
    ("Px10E", "SAVE", "contribute()"),
    ("Px10F", "SAVE", "contribute()"),
)

Fallout: Branches = (
    ("Px5", "SAVE", "Fal1out()"),
    ("Px23", "VIEW", "owner()"),
    ("Px139", "SAVE", "collectAllocations()"),
    ("Px9F", "SAVE", "collectAllocations()"),
    ("Px83", "SAVE", "allocate()"),
    ("Px10F9", "SAVE", "sendAllocation(address)"),
    ("Px87F", "SAVE", "sendAllocation(address)"),
    ("Px40F", "VIEW", "allocatorBalance(address)"),
)

CoinFlip: Branches = (
    ("Px6FF", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px6FD", "SAVE", "flip(bool)"),
    ("PxDF9", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px19", "VIEW", "consecutiveWins()"),
)

Telephone: Branches = (
    ("PxD", "VIEW", "owner()"),
    ("PxCF", "VIEW", "changeOwner(address)"),
    ("PxCE", "SAVE", "changeOwner(address)"),
)

Token: Branches = (
    ("PxD", "VIEW", "totalSupply()"),
    ("Px33", "VIEW", "balanceOf(address)"),
    ("PxC7", "SAVE", "transfer(address,uint256)"),
)

Delegation: Branches = (
    ("Px331", "VIEW", "$any4"),  # *
    ("Px333", "SAVE", "pwn()"),
    ("PxD", "VIEW", "owner()"),
    ("Px7F", "VIEW", None),  # *
    # * if Delegate reverts, Delegation will still return successfully
)

Force: Branches = ()

Vault: Branches = (
    ("PxD", "VIEW", "locked()"),
    ("PxCF", "VIEW", "unlock(bytes32)"),
    ("PxCE", "SAVE", "unlock(bytes32)"),
)

King: Branches = (
    ("PxB", "VIEW", "_king()"),
    ("Px13", "VIEW", "owner()"),
    ("PxC9", "SAVE", None, None),
    ("PxD9", "SAVE", None, None),
    ("Px23", "VIEW", "prize()"),
    ("Px6F", "SAVE", None, None),
    ("Px67", "SAVE", None, None),
)

Reentrancy: Branches = (
    ("Px6", "VIEW", None),
    ("Px2F", "SAVE", "donate(address)"),
    ("Px4F", "VIEW", "balances(address)"),
    ("Px11F", "VIEW", "withdraw(uint256)"),
    ("Px10F", "VIEW", "balanceOf(address)"),
    ("Px8F5", "SAVE", "withdraw(uint256)"),
    ("Px8F7", "SAVE", "withdraw(uint256)"),
    ("Px11E3", "SAVE", "withdraw(uint256)"),
    ("Px11E7", "SAVE", "withdraw(uint256)"),
)

Elevator: Branches = (
    ("PxD", "VIEW", "floor()"),
    ("Px31", "VIEW", "top()"),
    ("PxCFF", "VIEW", "goTo(uint256)"),
    ("PxCFEF", "SAVE", "goTo(uint256)"),
)

Privacy: Branches = (
    ("PxD", "VIEW", "ID()"),
    ("Px19", "VIEW", "locked()"),
    ("Px18F", "SAVE", "unlock(bytes16)"),
)

GatekeeperOne: Branches = (
    ("PxDFF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

GatekeeperTwo: Branches = (
    ("Px1BF", "SAVE", "enter(bytes8)"),
    ("Px19", "VIEW", "entrant()"),
)

Preservation: Branches = (
    ("PxC1CEF", "SAVE", "setFirstTime(uint256)"),
    ("Px61", "VIEW", "owner()"),
    ("Px31CEF", "SAVE", "setSecondTime(uint256)"),
    ("Px19", "VIEW", "timeZone1Library()"),
    ("PxD", "VIEW", "timeZone2Library()"),
)


def delegation_start(programs: dict[str, Program]) -> State:
    """Set up the Delegation level."""
    other = Contract(address=Uint160(0xABCDEF), program=programs["Delegate"])
    start = symbolic_start(programs["Delegation"], SHA3(), "").with_contract(other)
    start.balances[start.transaction.address] = start.transaction.callvalue
    start.storage[Uint256(1)] = other.address.into(Uint256)
    return start


def preservation_start(programs: dict[str, Program]) -> State:
    """Set up the Preservation level."""
    preservation = Contract(program=programs["Preservation"])
    library = Contract(
        address=Uint160(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    start = symbolic_start(preservation.program, SHA3(), "").with_contract(library)
    start.balances[start.transaction.address] = start.transaction.callvalue
    start.storage[Uint256(0)] = library.address.into(Uint256)
    start.storage[Uint256(1)] = library.address.into(Uint256)
    return start
