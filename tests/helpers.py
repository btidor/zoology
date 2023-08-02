"""Test helpers, mostly related to fixtures."""

from disassembler import Program
from environment import Contract
from smt.sha3 import SHA3
from smt.smt import BitVector, Uint160, Uint256
from state import State
from universal import symbolic_start


def concretize(value: BitVector | None) -> int | None:
    """Unwrap the given value, passing through Nones."""
    if value is None:
        return None
    return value.unwrap()


Fallback = (
    ("Px19", "SAVE", None, 1),
    ("Px2F", "SAVE", "withdraw()"),
    ("Px4F", "VIEW", "contributions(address)"),
    ("Px23", "VIEW", "owner()"),
    ("Px10F", "SAVE", "contribute()"),
    ("Px10E", "SAVE", "contribute()"),
    ("Px83", "VIEW", "getContribution()"),
)

Fallout = (
    ("Px5", "SAVE", "Fal1out()"),
    ("Px4F", "SAVE", "collectAllocations()"),
    ("Px23", "VIEW", "owner()"),
    ("Px43F", "SAVE", "sendAllocation(address)"),
    ("Px83", "SAVE", "allocate()"),
    ("Px40F", "VIEW", "allocatorBalance(address)"),
)

CoinFlip = (
    ("Px6FF", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px6FD", "SAVE", "flip(bool)"),
    ("PxDF9", "SAVE", "flip(bool)"),
    ("PxDFD", "SAVE", "flip(bool)"),
    ("Px19", "VIEW", "consecutiveWins()"),
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
    ("Px191", "VIEW", "$any4"),  # *
    ("Px193", "SAVE", "pwn()"),
    ("Px67", "VIEW", "$any4"),  # *
    ("PxD", "VIEW", "owner()"),
    ("Px3F", "VIEW", None),  # *
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
    ("Px47B", "SAVE", "withdraw(uint256)"),
    ("Px479", "SAVE", "withdraw(uint256)"),
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
    ("Px60E6F", "SAVE", "setFirstTime(uint256)"),
    ("Px61", "VIEW", "owner()"),
    ("Px18E6F", "SAVE", "setSecondTime(uint256)"),
    ("Px19", "VIEW", "timeZone1Library()"),
    ("PxD", "VIEW", "timeZone2Library()"),
)


def delegation_start(programs: dict[str, Program]) -> State:
    """Set up the Delegation level."""
    other = Contract(address=Uint160(0xABCDEF), program=programs["Delegate"])
    start = symbolic_start(programs["Delegation"], SHA3(), "")
    start.transfer(
        start.transaction.caller, start.contract.address, start.transaction.callvalue
    )
    start.universe.add_contract(other)
    start.contract.storage.poke(Uint256(1), other.address.into(Uint256))
    return start


def preservation_start(programs: dict[str, Program]) -> State:
    """Set up the Preservation level."""
    preservation = Contract(program=programs["Preservation"])
    library = Contract(
        address=Uint160(0x1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B1B),
        program=programs["LibraryContract"],
    )

    start = symbolic_start(preservation.program, SHA3(), "")
    start.transfer(
        start.transaction.caller, start.contract.address, start.transaction.callvalue
    )
    start.universe.add_contract(library)
    start.contract.storage.poke(Uint256(0), library.address.into(Uint256))
    start.contract.storage.poke(Uint256(1), library.address.into(Uint256))
    return start
