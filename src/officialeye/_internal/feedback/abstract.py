from __future__ import annotations

from abc import ABC, abstractmethod
from concurrent.futures import Future
from types import TracebackType
from typing import TYPE_CHECKING, Any

from officialeye._internal.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye._internal._types import RichProtocol


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
    ) -> None:
        raise NotImplementedError()

    @abstractmethod
    def info(self, verbosity: Verbosity, message: str, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def warn(self, verbosity: Verbosity, message: str, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def error(self, verbosity: Verbosity, message: str, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def update_status(self, new_status_text: str, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def dispose(self, exception_type: any = None, exception_value: BaseException | None = None, traceback: TracebackType | None = None) -> None:
        raise NotImplementedError()

    @abstractmethod
    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        raise NotImplementedError()

    @abstractmethod
    def join(self, child: AbstractFeedbackInterface, future: Future, /) -> None:
        raise NotImplementedError()
