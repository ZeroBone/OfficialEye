from __future__ import annotations

from abc import ABC, abstractmethod
from concurrent.futures import Future
from typing import Any, TYPE_CHECKING

from officialeye._api.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye._types import RichProtocol


class AbstractFeedbackInterface(ABC):

    def __init__(self, verbosity: Verbosity, /):
        self._verbosity = verbosity

    @abstractmethod
    def echo(
        self,
        verbosity: Verbosity,
        message: str | RichProtocol = "", /, *,
        err: bool = False,
        **kwargs: Any
    ):
        raise NotImplementedError()

    @abstractmethod
    def info(self, verbosity: Verbosity, message: str, /):
        raise NotImplementedError()

    @abstractmethod
    def warn(self, verbosity: Verbosity, message: str, /):
        raise NotImplementedError()

    @abstractmethod
    def error(self, verbosity: Verbosity, message: str, /):
        raise NotImplementedError()

    @abstractmethod
    def dispose(self):
        raise NotImplementedError()

    @abstractmethod
    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        raise NotImplementedError()

    @abstractmethod
    def join(self, child: AbstractFeedbackInterface, future: Future, /):
        raise NotImplementedError()
