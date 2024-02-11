import enum
from concurrent.futures import Future

# noinspection PyProtectedMember
from multiprocessing.connection import Connection
from types import TracebackType
from typing import Any

# noinspection PyProtectedMember
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity


class IPCMessageType(enum.IntEnum):
    ECHO = 0
    INFO = 1
    WARN = 2
    ERROR = 3

    UPDATE_STATUS = 4
    # means that the task is completed in any way, including throwing an exception
    TASK_DONE = 5


class InternalFeedbackInterface(AbstractFeedbackInterface):

    def __init__(self, verbosity: Verbosity, child_id: int, tx: Connection, /):
        super().__init__(verbosity)

        assert tx is not None

        self._child_id = child_id
        self._tx = tx

    def get_child_id(self) -> int:
        return self._child_id

    def _send_ipc_message(self, message_type: IPCMessageType, *args, **kwargs):
        ipc_message = (message_type, args, kwargs)
        self._tx.send(ipc_message)

    def echo(self, *args: Any, **kwargs: Any) -> None:
        self._send_ipc_message(IPCMessageType.ECHO, *args, **kwargs)

    def info(self, *args: Any, **kwargs: Any) -> None:
        self._send_ipc_message(IPCMessageType.INFO, *args, **kwargs)

    def warn(self, *args: Any, **kwargs: Any) -> None:
        self._send_ipc_message(IPCMessageType.WARN, *args, **kwargs)

    def error(self, *args: Any, **kwargs: Any) -> None:
        self._send_ipc_message(IPCMessageType.ERROR, *args, **kwargs)

    def update_status(self, new_status_text: str, /) -> None:
        self._send_ipc_message(IPCMessageType.UPDATE_STATUS, new_status_text)

    def dispose(self, exception_type: any = None, exception_value: BaseException | None = None, traceback: TracebackType | None = None) -> None:

        task_done_successfully: bool = exception_value is None

        self._send_ipc_message(IPCMessageType.TASK_DONE, task_done_successfully)

        self._tx.close()

    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        # the internal feedback interface isn't meant to be forked
        raise NotImplementedError()

    def join(self, child: AbstractFeedbackInterface, future: Future, /) -> None:
        # the internal feedback interface isn't meant to be forked, so it cannot be joined either
        raise NotImplementedError()
