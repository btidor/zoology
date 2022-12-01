from typing import Callable, NoReturn, Optional, cast

import z3

from _state import State
from _symbolic import BW


def assert_never(value: NoReturn) -> NoReturn:
    # TODO: remove me in Python 3.11
    assert False, f"unknown enum value: {value}"


class Predicate:
    def __init__(
        self,
        expression: Callable[[State], z3.ExprRef],
        description: str,
        state: State,
        storage_key: Optional[z3.ExprRef] = None,
    ) -> None:
        self.expression = expression
        self.description = description
        self.state = state
        self.storage_key = storage_key

    def eval(self, state: State) -> z3.ExprRef:
        return self.expression(state)

    def __repr__(self) -> str:
        return self.description
