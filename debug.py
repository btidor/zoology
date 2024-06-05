#!/usr/bin/env python3
"""Helper tools for debugging."""

import argparse

from disassembler import Program
from snapshot import LEVEL_FACTORIES, snapshot_contracts
from state import Jump
from vm import step
from zoology import make_heads, starting_sequence


def do_code(level: int) -> None:
    """Print the instance code for the given level."""
    factory = LEVEL_FACTORIES[level]
    contracts = snapshot_contracts(factory)
    beginning = starting_sequence(contracts, factory)

    for contract in beginning.states[-1].contracts.values():
        if contract.invisible:
            continue
        x = "*" if (contract.address == beginning.instance).reveal() else ""
        print(str(contract.address) + x)
        assert (code := contract.program.code.reveal()) is not None
        print("-", code.hex())


def do_trace(level: int, path: int) -> None:
    """Print the jumps corresponding to a given path."""
    factory = LEVEL_FACTORIES[level]
    contracts = snapshot_contracts(factory)
    beginning = starting_sequence(contracts, factory)

    for state in make_heads(beginning):
        print(state.transaction.address)
        i = int.bit_length(path) - 2
        while isinstance(state.pc, int):
            before = state.pc
            ins = state.program.instructions[before]
            match step(state):
                case None:
                    pass
                case Jump(targets):
                    assert len(targets) == 2
                    if path & (1 << i) == 0:
                        state = targets[0]
                    else:
                        state = targets[1]
                    i -= 1
                case _:
                    raise NotImplementedError
            if ins.name in ("JUMP", "JUMPI"):
                assert isinstance(state.pc, int)
                print(
                    f"{_offset(state.program, before)}  {ins.name:5}  {_offset(state.program, state.pc)}"
                )


def _offset(program: Program, pc: int) -> str:
    ins = program.instructions[pc]
    return ins.offset.to_bytes(2).hex().upper()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command")
    code = commands.add_parser("code")
    code.add_argument("level", type=int)

    trace = commands.add_parser("trace")
    trace.add_argument("level", type=int)
    trace.add_argument("path")

    args = parser.parse_args()
    match args.command:
        case "code":
            do_code(args.level)
        case "trace":
            if args.path is None:
                raise ValueError("path is required")
            elif args.path.startswith("P"):
                p = int(args.path[2:], 16)
            else:
                p = int(args.path, 16)
            do_trace(args.level, p)
        case _:
            parser.print_help()
