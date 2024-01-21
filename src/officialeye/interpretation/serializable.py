from typing import TypeAlias

Serializable: TypeAlias = dict[str, "Serializable"] | list["Serializable"] | str | int | float | bool | None
