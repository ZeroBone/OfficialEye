import enum
from concurrent.futures import Future
# noinspection PyProtectedMember
from multiprocessing.connection import Connection
from typing import Any

# noinspection PyProtectedMember
from officialeye._api.feedback.abstract import AbstractFeedbackInterface
# noinspection PyProtectedMember
from officialeye._api.feedback.verbosity import Verbosity


class IPCMessageType(enum.IntEnum):
    ECHO = 0
    INFO = 1
    WARN = 2
    ERROR = 3
    UPDATE_PROGRESS = 4
    CLOSE = 5


class InternalFeedbackInterface(AbstractFeedbackInterface):

    def __init__(self, verbosity: Verbosity, tx: Connection, /):
        super().__init__(verbosity)

        self._tx = tx

    def _send_ipc_message(self, message_type: IPCMessageType, *args, **kwargs):
        ipc_message = (message_type, args, kwargs)
        self._tx.send(ipc_message)

    def echo(self, *args: Any, **kwargs: Any):
        self._send_ipc_message(IPCMessageType.ECHO, *args, **kwargs)

    def info(self, *args: Any, **kwargs: Any):
        self._send_ipc_message(IPCMessageType.INFO, *args, **kwargs)

    def warn(self, *args: Any, **kwargs: Any):
        self._send_ipc_message(IPCMessageType.WARN, *args, **kwargs)

    def error(self, *args: Any, **kwargs: Any):
        self._send_ipc_message(IPCMessageType.ERROR, *args, **kwargs)

    def dispose(self):
        self._send_ipc_message(IPCMessageType.CLOSE)
        self._tx.close()

    def fork(self, description: str, /) -> AbstractFeedbackInterface:
        # the internal feedback interface isn't meant to be forked
        raise NotImplementedError()

    def join(self, child: AbstractFeedbackInterface, future: Future, /):
        # the internal feedback interface isn't meant to be forked, so it cannot be joined either
        raise NotImplementedError()
