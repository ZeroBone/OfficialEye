from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Union

if TYPE_CHECKING:
    ConfigValue = Union[str, int, float, Dict[str, "ConfigValue"]]
    ConfigDict = Dict[str, ConfigValue]
