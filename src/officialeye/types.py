from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Union, Callable

# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator
# noinspection PyProtectedMember
from officialeye._api.template.matcher import IMatcher
# noinspection PyProtectedMember
from officialeye._api.template.supervisor import ISupervisor


if TYPE_CHECKING:
    ConfigValue = Union[str, int, float, Dict[str, "ConfigValue"]]
    ConfigDict = Dict[str, ConfigValue]

    MutatorFactory = Callable[[ConfigDict], IMutator]
    MatcherFactory = Callable[[ConfigDict], IMatcher]
    SupervisorFactory = Callable[[ConfigDict], ISupervisor]
