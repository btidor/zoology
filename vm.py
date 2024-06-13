#!/usr/bin/env python3
"""A machine to execute compiled symbolic programs."""

from typing import Iterable

from zbitvector import Solver

from bytes import Bytes
from compiler import compile
from disassembler import Program, abiencode, disassemble
from smt import Array, Uint8, Uint64, Uint160, Uint256, substitute
from state import Block, State, Termination


def execute(
    state: State, block: Block, input: Bytes, storage: Array[Uint256, Uint256]
) -> State:
    """Substitute concrete values in a candidate state transition."""
    return substitute(
        state,
        [
            # Block
            (Uint256("NUMBER"), block.number),
            (Uint160("COINBASE"), block.coinbase),
            (Uint256("TIMESTAMP"), block.timestamp),
            (Uint256("PREVRANDAO"), block.prevrandao),
            (Uint256("GASLIMIT"), block.gaslimit),
            (Uint256("CHAINID"), block.chainid),
            (Uint256("BASEFEE"), block.basefee),
            (Array[Uint8, Uint256]("BLOCKHASH"), block.hashes),
            # Transaction
            (Uint160("ORIGIN"), Uint160(0xC0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0C0)),
            (Uint160("CALLER"), Uint160(0xCACACACACACACACACACACACACACACACACACACACA)),
            (Uint160("ADDRESS"), Uint160(0xADADADADADADADADADADADADADADADADADADADAD)),
            (Uint256("CALLVALUE"), Uint256(0)),
            (Array[Uint256, Uint8]("CALLDATA"), input.array),
            (Uint64("CALLDATA.length"), input.length.into(Uint64)),
            (Uint256("GASPRICE"), Uint256(0x12)),
            # State
            (Array[Uint256, Uint256]("STORAGE"), storage),
            (Array[Uint160, Uint256]("BALANCE"), Array[Uint160, Uint256](Uint256(0))),
        ],
    )


def printable_execution(
    program: Program, calldata: bytes, slots: dict[int, int]
) -> Iterable[str]:
    """Produce a human-readable transcript of execution."""
    block, input = Block.sample(0), Bytes(calldata)
    storage = Array[Uint256, Uint256](Uint256(0))
    for k, v in slots.items():
        storage[Uint256(k)] = Uint256(v)

    for state in compile(program):
        state = execute(state, block, input, storage)

        solver = Solver()
        solver.add(state.constraint)
        if not solver.check():
            continue

        assert isinstance(state.pc, Termination)
        yield f"{state.px()}\t{state.pc.success} {state.pc.returndata.evaluate(solver).hex()}"


if __name__ == "__main__":
    code = Bytes.fromhex(
        "608060405234801561001057600080fd5b50600436106100365760003560e01c80631d263f671461003b578063e6f334d714610063575b600080fd5b61004e610049366004610101565b61007a565b60405190151581526020015b60405180910390f35b61006c60005481565b60405190815260200161005a565b600080610088600143610140565b6001549040915081141561009b57600080fd5b60018190556002546000906100b09083610157565b90506000816001146100c35760006100c6565b60015b905084151581151514156100f3576000805490806100e383610179565b9091555060019695505050505050565b505060008080559392505050565b60006020828403121561011357600080fd5b8135801515811461012357600080fd5b9392505050565b634e487b7160e01b600052601160045260246000fd5b6000828210156101525761015261012a565b500390565b60008261017457634e487b7160e01b600052601260045260246000fd5b500490565b600060001982141561018d5761018d61012a565b506001019056fea264697066735822122019b0acf2cc7b361011e29b3b4d16427ec001905ffbf2afb78ffbc731c4e4b5ff64736f6c634300080c0033"
    )
    program = disassemble(code)
    calldata = abiencode("flip(bool)") + (1).to_bytes(32)
    slots = {
        2: 57896044618658097711785492504343953926634992332820282019728792003956564819968
    }
    for line in printable_execution(program, calldata, slots):
        print(line)
