#!/usr/bin/env python3

import inspect
from typing import Dict, List, Tuple, cast

import z3

import ops
from common import BW, Address, ByteArray, Instruction, State, uint256
from disassembler import disassemble

SOLVER = z3.Solver()


class ZeroWorld(ops.World):
    def balance(self, address: Address) -> uint256:
        return BW(0)

    def code(self, address: Address) -> bytes:
        return b""

    def blockhash(self, blockNumber: int) -> int:
        return 123456


WORLD = ZeroWorld()


def analyze(
    instructions: List[Instruction],
    jumps: Dict[int, int],
    value: int,
    data: ByteArray,
) -> None:
    s = State(jumps=jumps, callvalue=value, calldata=data)
    stack: List[uint256] = []
    states = [(s, stack)]

    while len(states) > 0:
        s, stack = states.pop()
        if s.success is not None:
            print("TERMINAL STATE")
            v = z3.Optimize()
            v.add(s.constraints)
            v.minimize(value)
            v.minimize(data.length())
            assert v.check() == z3.sat
            m = v.model()
            print("Value:", m.eval(value))
            print("Len  :", m.eval(data.length()))
            print("Data : ", end="")
            for i in range(m.eval(data.length()).as_long()):
                b = m.eval(data.get(i))
                if z3.is_bv_value(b):
                    print(b.as_long().to_bytes(1, "big").hex(), end="")
                else:
                    print("??", end="")
            print("")
            print("RETURN" if s.success else "REVERT", s.returndata)
            print()
            continue
        states += execute(instructions, s, stack)

    print("#### DONE")


def execute(
    instructions: List[Instruction],
    s: State,
    stack: List[uint256],
) -> List[Tuple[State, List[uint256]]]:
    while s.success is None:
        ins = instructions[s.pc]
        s.pc += 1

        # msg = f"{(s.pc-1):04} {ins.name}"
        # if ins.suffix is not None:
        #     msg += str(ins.suffix)
        # if ins.operand is not None:
        #     msg += "\t" + hex(ins.operand.as_long())
        # print(msg)

        if ins.name == "PUSH":
            stack.append(ins.operand)
        elif ins.name == "DUP":
            # TODO: handle out-of-range
            n = cast(int, ins.suffix)
            stack.append(stack[-n])
        elif ins.name == "SWAP":
            # TODO: handle out-of-range
            n = cast(int, ins.suffix) + 1
            stack[-1], stack[-n] = stack[-n], stack[-1]
        elif ins.name == "JUMPI":
            counter = ops.require_concrete(
                stack.pop(), "JUMPI(counter, b) requires concrete counter"
            )
            b = z3.simplify(stack.pop())

            next = []
            constraints1 = z3.And(s.constraints, b == 0)
            if SOLVER.check(constraints1) == z3.sat:
                s1, stack1 = s.copy(), stack.copy()
                s1.constraints = constraints1
                next.append((s1, stack1))
            constraints2 = z3.And(s.constraints, b != 0)
            if SOLVER.check(constraints2) == z3.sat:
                s2, stack2 = s.copy(), stack.copy()
                s2.pc = s2.jumps[counter]
                s2.constraints = constraints2
                next.append((s2, stack2))
            return next
        elif ins.name == "PC":
            stack.append(ins.operand)
        elif ins.name == "CALL":
            pass  # TODO
        elif hasattr(ops, ins.name):
            fn = getattr(ops, ins.name)
            sig = inspect.signature(fn)
            args: List[object] = []
            for name in sig.parameters:
                kls = sig.parameters[name].annotation
                if kls == uint256:
                    # TODO: handle pop from empty list
                    args.append(stack.pop())
                elif kls == State:
                    args.append(s)
                elif kls == ops.World:
                    args.append(WORLD)
                else:
                    raise TypeError(f"unknown arg class: {kls}")
            r = fn(*args)
            if r is not None:
                stack.append(r)
        else:
            raise ValueError(f"unimplemented opcode: {ins.name}")

        # for x in stack:
        #     x = z3.simplify(x)
        #     if z3.is_bv_value(x):
        #         print(" ", x.as_long().to_bytes(32, "big").hex())
        #     else:
        #         print(" ", x)
        # print()

    return [(s, stack)]


if __name__ == "__main__":
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    instructions, jumps = disassemble(code)
    analyze(instructions, jumps, BW(0), ByteArray("CALLDATA"))