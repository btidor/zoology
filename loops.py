#!/usr/bin/env python3
"""A helper to extract and flatten common copy-loops."""

from itertools import chain
from typing import Any

from bytes import Bytes
from disassembler import Instruction, LoopCopy, Program, disassemble
from ops import OPS
from smt import Uint, Uint256
from state import State


def flatten_loops(program: Program) -> Program:
    """Extract and flattens common write patterns."""
    instructions = list(program.instructions)
    for offset, pc in program.jumps.items():
        try:
            result = analyze_block(program, pc)
        except Exception:
            continue
        if isinstance(result, str):
            continue
        instructions[pc] = Instruction(offset, 0, "CUSTOM", None, custom=result)
    return Program(program.code, tuple(instructions), program.jumps)


class AnalysisError(Exception):
    """An error occurred during program analysis."""

    pass


def analyze_block(program: Program, start: int) -> LoopCopy:
    """Determine if a given basic block represents a supported write pattern."""
    stack = [Uint256(f"STACK{n}") for n in reversed(range(8))]
    pc = start
    actions: list[tuple[Any, ...]] = []
    count = 0

    while True:
        assert isinstance(pc, int)
        if count > 0 and pc == start:
            return check_candidate(actions, stack)

        ins = program.instructions[pc]
        pc += 1

        match ins.name:
            case "DUP":
                assert ins.suffix is not None
                stack.append(stack[-ins.suffix])
            case "SWAP":
                assert ins.suffix is not None
                m = ins.suffix + 1
                stack[-1], stack[-m] = stack[-m], stack[-1]
            case "JUMP":
                counter = stack.pop().reveal()
                assert counter is not None, "JUMP requires concrete counter"
                pc = program.jumps[counter]
            case "JUMPI":
                counter = stack.pop().reveal()
                assert counter is not None, "JUMPI requires concrete counter"
                cond = stack.pop() == Uint256(0)
                match cond.reveal():
                    case None:  # unknown, must prepare both branches :(
                        if count == 0:
                            actions.append(("JUMPI", counter, cond))
                            count += 1
                        else:
                            raise AnalysisError("not found")
                        if counter == start:
                            return check_candidate(actions, stack)
                    case True:  # branch never taken, fall through
                        pass
                    case False:  # branch always taken
                        pc = program.jumps[counter]
            case "MLOAD":
                actions.append(("MLOAD", stack.pop()))
                stack.append(Uint256("LOAD"))
            case "MSTORE":
                store = stack.pop()
                value = stack.pop()
                actions.append(("MSTORE", store, value))
            case _:
                if ins.name not in OPS:
                    raise ValueError(f"unimplemented opcode: {ins.name}")

                fn, sig = OPS[ins.name]
                args = list[object]()
                for name in sig.parameters:
                    kls = sig.parameters[name].annotation
                    if kls == Uint256:
                        val = stack.pop()
                        args.append(val)
                    elif kls == State:
                        raise AnalysisError(f"unsupported op: {ins.name}")
                    elif kls == Instruction:
                        args.append(ins)
                    else:
                        raise TypeError(f"unknown arg class: {kls}")

                result = fn(*args)
                if result is not None:
                    assert isinstance(result, Uint)
                    stack.append(result)


def check_candidate(ops: list[tuple[Any, ...]], stack: list[Uint256]) -> LoopCopy:
    """Check a given write pattern is supported."""
    # For now, only the JUMP-LOAD-STORE ordering is supported.
    sequence = [x[0] for x in ops]
    if sequence != ["JUMPI", "MLOAD", "MSTORE"]:
        raise AnalysisError(f"unsupported sequence: {sequence}")
    jump, load, store = ops

    # The stack must not grow or shrink. Otherwise, after many iterations it
    # will overflow or empty.
    starting_stack = [Uint256(f"STACK{n}") for n in reversed(range(8))]
    if len(stack) != len(starting_stack):
        raise AnalysisError(f"stack size changed: {stack}")

    # For now, only support loops where the top stack variable is the iteration
    # counter, and no other stack variable changes.
    for original, final in zip(starting_stack[:-1], stack[:-1]):
        if (original == final).reveal() is not True:
            raise AnalysisError(f"substack changed: {original} -> {final}")

    stride: Uint256 | None = None
    for var in chain(starting_stack[:-1], (Uint256(0x20),)):
        expected, actual = starting_stack[-1] + var, stack[-1]
        if (expected == actual).reveal() is True:
            stride = var
            break
    if stride is None:
        raise AnalysisError(f"unsupported stride: {stack[-1]}")

    # We expect the iteration counter to increase until some (exclusive) limit
    # represented by a variable on the stack.
    _, exit, cond = jump
    limit: Uint256 | None = None
    for var in starting_stack[:-1]:
        test = starting_stack[-1] < var
        if (cond == test).reveal() is True:
            limit = var
            break
    if limit is None:
        raise AnalysisError(f"unsupported limit: {cond}")

    # HACK: we plug in the starting values of the stack to get the initial
    # read/write addresses, then assume the reads/writes are contiguous from
    # there. This is true if offsets are computed with addition and do not
    # overflow. We also assume the read/writes do not overlap.

    if (store[2] == Uint256("LOAD")).reveal() is not True:
        raise AnalysisError(f"unsupported store: {store[2]}")

    return LoopCopy(starting_stack[-1], limit, stride, load[1], store[1], exit)


if __name__ == "__main__":
    code = Bytes(
        bytes.fromhex(
            "60806040526004361061006e575f3560e01c8063817b1cd21161004c578063817b1cd2146100e9578063ad5c4648146100fd578063ede85eb714610134578063f1f1db1e14610162575f80fd5b80636e35c7401461007257806378e7ed2f146100a65780637b233319146100b0575b5f80fd5b34801561007d575f80fd5b5061009161008c366004610632565b610181565b60405190151581526020015b60405180910390f35b6100ae610422565b005b3480156100bb575f80fd5b506100db6100ca366004610649565b60016020525f908152604090205481565b60405190815260200161009d565b3480156100f4575f80fd5b506100db5f5481565b348015610108575f80fd5b5060035461011c906001600160a01b031681565b6040516001600160a01b03909116815260200161009d565b34801561013f575f80fd5b5061009161014e366004610649565b60026020525f908152604090205460ff1681565b34801561016d575f80fd5b5061009161017c366004610632565b6104cb565b5f66038d7ea4c6800082116101dd5760405162461bcd60e51b815260206004820152600e60248201527f446f6e277420626520636865617000000000000000000000000000000000000060448201526064015b60405180910390fd5b600354604080513360248201523060448083019190915282518083039091018152606490910182526020810180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff167fdd62ed3e0000000000000000000000000000000000000000000000000000000017905290515f926001600160a01b03169161026491610676565b5f604051808303815f865af19150503d805f811461029d576040519150601f19603f3d011682016040523d82523d5f602084013e6102a2565b606091505b50915050826102b0826105b1565b10156102fe5760405162461bcd60e51b815260206004820181905260248201527f486f7720616d2049206d6f76696e67207468652066756e647320686f6e65793f60448201526064016101d4565b825f8082825461030e91906106cf565b9091555050335f90815260016020526040812080548592906103319084906106cf565b909155505060035460408051336024820152306044820152606480820187905282518083039091018152608490910182526020810180517bffffffffffffffffffffffffffffffffffffffffffffffffffffffff167f23b872dd0000000000000000000000000000000000000000000000000000000017905290515f926001600160a01b0316916103c191610676565b5f604051808303815f865af19150503d805f81146103fa576040519150601f19603f3d011682016040523d82523d5f602084013e6103ff565b606091505b5050335f908152600260205260409020805460ff19166001179055949350505050565b66038d7ea4c6800034116104785760405162461bcd60e51b815260206004820152600e60248201527f446f6e277420626520636865617000000000000000000000000000000000000060448201526064016101d4565b345f8082825461048891906106cf565b9091555050335f90815260016020526040812080543492906104ab9084906106cf565b9091555050335f908152600260205260409020805460ff19166001179055565b335f908152600160205260408120548211156105295760405162461bcd60e51b815260206004820152600f60248201527f446f6e277420626520677265656479000000000000000000000000000000000060448201526064016101d4565b335f90815260016020526040812080548492906105479084906106e8565b92505081905550815f8082825461055e91906106e8565b90915550506040515f90339084908381818185875af1925050503d805f81146105a2576040519150601f19603f3d011682016040523d82523d5f602084013e6105a7565b606091505b5090949350505050565b5f60208251101561062a5760405162461bcd60e51b815260206004820152602560248201527f44617461206c656e677468206d757374206265206174206c656173742033322060448201527f627974657300000000000000000000000000000000000000000000000000000060648201526084016101d4565b506020015190565b5f60208284031215610642575f80fd5b5035919050565b5f60208284031215610659575f80fd5b81356001600160a01b038116811461066f575f80fd5b9392505050565b5f82515f5b81811015610695576020818601810151858301520161067b565b505f920191825250919050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601160045260245ffd5b808201808211156106e2576106e26106a2565b92915050565b818103818111156106e2576106e26106a256fea2646970667358221220c65c29ae014367df4445299bd1a81e485bac5be1083a3e141b3b6a0631dee96b64736f6c63430008170033"
        )
    )
    program = disassemble(code)

    for offset, pc in program.jumps.items():
        print(offset.to_bytes(2).hex().upper(), end="")
        try:
            r = analyze_block(program, pc)
            print(f"\t{r}")
        except Exception as e:
            print(f"\t{e}")

# *00 047B [('JUMPI', 1171, Constraint(`(bvult STACK0 STACK3)`)), ('MLOAD', Uint256(`(bvadd STACK0 STACK1)`)), ('MSTORE', Uint256(`(bvadd STACK0 STACK2)`), Uint256(`LOAD`))]
#          STACK0 += 0x20
#  15 0876 [('JUMPI', 2194, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd STACK2 (bvadd STACK0 STACK5))`)), ('MSTORE', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd STACK0 STACK4))`), Uint256(`LOAD`))]
#          STACK0 += STACK2
#  16 01C1 [('JUMPI',  475, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000020 (bvadd STACK0 STACK4))`)), ('MSTORE', Uint256(`(bvadd STACK0 STACK3)`), Uint256(`LOAD`))]
#          STACK0 += 0x20
# *17 0184 [('JUMPI',  417, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000020 (bvadd STACK0 STACK6))`)), ('MSTORE', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000080 (bvadd STACK0 STACK3))`), Uint256(`LOAD`))]
#          STACK0 += 0x20
#    '02B3 [('JUMPI', 719, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd STACK2 (bvadd STACK0 STACK5))`)), ('MSTORE', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd STACK0 STACK4))`), Uint256(`LOAD`))]
#          STACK0 += STACK2
# *23'085F [('JUMPI', 2171, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd STACK2 (bvadd STACK0 STACK5))`)), ('MSTORE', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd STACK0 STACK4))`), Uint256(`LOAD`))]
#          STACK0 += STACK2
# *24 ???
# *25'0305 [('JUMPI',  804, Constraint(`(not (bvult STACK2 #x0000000000000000000000000000000000000000000000000000000000000020))`)), ('MLOAD', Uint256(`STACK0`)), ('MSTORE', Uint256(`STACK1`), Uint256(`LOAD`))]
#          STACK0 += 0x20   STACK1 += 0x20  STACK2 -= 0x20
#  26 0D45 [('JUMPI', 3425, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd STACK2 (bvadd STACK0 STACK5))`)), ('MSTORE', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000040 (bvadd STACK0 STACK4))`), Uint256(`LOAD`))]
#          STACK0 += STACK2
# *29 0429 [('JUMPI', 1091, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000020 (bvadd STACK0 STACK4))`)), ('MSTORE', Uint256(`(bvadd STACK0 STACK3)`), Uint256(`LOAD`))]
#          STACK0 += 0x20
# *31 067B [('JUMPI', 1685, Constraint(`(bvult STACK0 STACK1)`)), ('MLOAD', Uint256(`(bvadd #x0000000000000000000000000000000000000000000000000000000000000020 (bvadd STACK0 STACK4))`)), ('MSTORE', Uint256(`(bvadd STACK0 STACK3)`), Uint256(`LOAD`))]
#          STACK0 += 0x40
