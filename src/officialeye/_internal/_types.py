from __future__ import annotations

from typing import TYPE_CHECKING, Any, TypeVar

if TYPE_CHECKING:
    from typing import Protocol

    SpinnerT = TypeVar("SpinnerT", bound="Spinner")

    class Spinner(Protocol):
        def update(self, text: str) -> None:
            ...

        def __enter__(self: SpinnerT) -> SpinnerT:
            ...

        def __exit__(self, *args: Any) -> None:
            ...

    class RichProtocol(Protocol):
        def __rich__(self) -> str:
            ...
