#!/usr/bin/env pytest

import pytest

from disassembler import disassemble
from sha3 import SHA3
from solver import DefaultSolver
from testlib import check_transition
from universal import constrain_to_goal, printable_transition, universal_transaction


def test_basic() -> None:
    code = bytes.fromhex("60FF60EE5560AA60AA03600E57005B60006000FD")
    program = disassemble(code)
    sha3 = SHA3()

    universal = universal_transaction(program, sha3, "")

    start, end = next(universal)
    assert end.success == True

    end.path_constraints.append(
        # This extra constraint makes the test deterministic
        start.universe.balances[end.contract.address]
        == 0x8000000000001
    )
    solver = DefaultSolver()
    end.constrain(solver)
    constrain_to_goal(solver, start, end)
    assert not solver.check()

    solver = DefaultSolver()
    end.constrain(solver)
    assert solver.check()

    raw = """
        ---  📒 SAVE\tRETURN\tPx2\t---------------------------------------------------------

        Caller\t0xcacacacacacacacacacacacacacacacacacacaca

        Address\t0xadadadadadadadadadadadadadadadadadadadad

        Balance\tR: 0xadadadadadadadadadadadadadadadadadadadad
        \t-> 0x8000000000001
        \tR: 0xcacacacacacacacacacacacacacacacacacacaca
        \t-> 0x0

        Storage\tW: 0xee -> 0xff (from 0x0)
    """.splitlines()
    fixture = map(lambda x: x[8:], raw[1:])

    for actual, expected in zip(printable_transition(start, end), fixture, strict=True):
        assert actual.strip(" ") == expected

    with pytest.raises(StopIteration):
        next(universal)


def test_fallout() -> None:
    code = bytes.fromhex(
        "6080604052600436106100655760003560e01c8063a2dea26f11610043578063a2dea26f146100ba578063abaa9916146100ed578063ffd40b56146100f557610065565b80636fab5ddf1461006a5780638aa96f38146100745780638da5cb5b14610089575b600080fd5b61007261013a565b005b34801561008057600080fd5b50610072610182565b34801561009557600080fd5b5061009e610210565b604080516001600160a01b039092168252519081900360200190f35b3480156100c657600080fd5b50610072600480360360208110156100dd57600080fd5b50356001600160a01b031661021f565b610072610285565b34801561010157600080fd5b506101286004803603602081101561011857600080fd5b50356001600160a01b03166102b1565b60408051918252519081900360200190f35b600180547fffffffffffffffffffffffff0000000000000000000000000000000000000000163317908190556001600160a01b03166000908152602081905260409020349055565b6001546001600160a01b031633146101e1576040805162461bcd60e51b815260206004820152601760248201527f63616c6c6572206973206e6f7420746865206f776e6572000000000000000000604482015290519081900360640190fd5b60405133904780156108fc02916000818181858888f1935050505015801561020d573d6000803e3d6000fd5b50565b6001546001600160a01b031681565b6001600160a01b03811660009081526020819052604090205461024157600080fd5b6001600160a01b03811660008181526020819052604080822054905181156108fc0292818181858888f19350505050158015610281573d6000803e3d6000fd5b5050565b3360009081526020819052604090205461029f90346102cc565b33600090815260208190526040902055565b6001600160a01b031660009081526020819052604090205490565b600082820183811015610326576040805162461bcd60e51b815260206004820152601b60248201527f536166654d6174683a206164646974696f6e206f766572666c6f770000000000604482015290519081900360640190fd5b939250505056fea264697066735822122008472e24693cfb431a0cbec77ce1c2c19216911e421de2df4e138648a9ce11c764736f6c634300060c0033"
    )
    program = disassemble(code)
    universal = universal_transaction(program, SHA3(), "")
    check_transition(*next(universal), 0xB, "SAVE", "0x6fab5ddf")
    check_transition(*next(universal), 0xAF, "GOAL", "0x8aa96f38")
    check_transition(*next(universal), 0x53, "VIEW", "0x8da5cb5b")
    check_transition(*next(universal), 0x9F, "GOAL", "0xa2dea26f")
    check_transition(*next(universal), 0x23, "SAVE", "0xabaa9916")
    check_transition(*next(universal), 0x87, "VIEW", "0xffd40b56")

    with pytest.raises(StopIteration):
        next(universal)
