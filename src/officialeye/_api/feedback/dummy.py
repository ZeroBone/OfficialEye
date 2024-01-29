from __future__ import annotations

from concurrent.futures import Future
from typing import Any, TYPE_CHECKING

from officialeye._api.feedback.abstract import AbstractFeedbackInterface
from officialeye._api.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye._types import RichProtocol


class DummyFeedbackInterface(AbstractFeedbackInterface):

    def __init__(self, /):
        super().__init__(Verbosity.QUIET)

    def echo(self, verbosity: Verbosity, message: str | RichProtocol = "", /, *, err: bool = False, **kwargs: Any):
        pass

    def info(self, verbosity: Verbosity, message: str, /):
        pass

    def warn(self, verbosity: Verbosity, message: str, /):
        pass

    def error(self, verbosity: Verbosity, message: str, /):
        pass

    def dispose(self):
        pass

    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        return DummyFeedbackInterface()

    def join(self, child: AbstractFeedbackInterface, future: Future, /):
        pass


