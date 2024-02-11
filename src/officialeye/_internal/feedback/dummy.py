from __future__ import annotations

from concurrent.futures import Future
from types import TracebackType
from typing import TYPE_CHECKING, Any

from officialeye._internal.feedback.abstract import AbstractFeedbackInterface
from officialeye._internal.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye._internal._types import RichProtocol


class DummyFeedbackInterface(AbstractFeedbackInterface):

    def __init__(self, /):
        super().__init__(Verbosity.QUIET)

    def echo(self, verbosity: Verbosity, message: str | RichProtocol = "", /, *, err: bool = False, **kwargs: Any) -> None:
        pass

    def info(self, verbosity: Verbosity, message: str, /) -> None:
        pass

    def warn(self, verbosity: Verbosity, message: str, /) -> None:
        pass

    def error(self, verbosity: Verbosity, message: str, /) -> None:
        pass

    def update_status(self, new_status_text: str, /) -> None:
        pass

    def dispose(self, exception_type: any = None, exception_value: BaseException | None = None, traceback: TracebackType | None = None) -> None:
        pass

    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        return DummyFeedbackInterface()

    def join(self, child: AbstractFeedbackInterface, future: Future, /) -> None:
        pass


