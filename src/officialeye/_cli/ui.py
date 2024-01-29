from __future__ import annotations

from concurrent.futures import Future
from multiprocessing import Pipe
# noinspection PyProtectedMember
from multiprocessing.connection import Connection, wait
from threading import Thread, Lock
from types import TracebackType
from typing import Any, TYPE_CHECKING, Dict, Tuple, List

from rich.console import Console
from rich.panel import Panel
from rich.theme import Theme
from rich.progress import Progress, SpinnerColumn, TextColumn, TaskID
from rich.traceback import Traceback

# noinspection PyProtectedMember
from officialeye._internal.context.feedback import InternalFeedbackInterface, IPCMessageType
from officialeye.error.error import OEError
from officialeye.error.errors.internal import ErrInternal
from officialeye.feedback import AbstractFeedbackInterface, Verbosity

if TYPE_CHECKING:
    from officialeye.feedback import RichProtocol

_THEME_TAG_INFO = "info"
_THEME_TAG_INFO_VERBOSE = "infov"
_THEME_TAG_DEBUG = "debug"
_THEME_TAG_DEBUG_VERBOSE = "debugv"

_THEME_TAG_WARN = "warn"
_THEME_TAG_ERR = "err"

_THEME: Dict[str, str] = {
    _THEME_TAG_INFO: "bold cyan",
    _THEME_TAG_INFO_VERBOSE: "green bold",
    _THEME_TAG_DEBUG: "cyan bold",
    _THEME_TAG_DEBUG_VERBOSE: "magenta bold",
    _THEME_TAG_WARN: "bold yellow",
    _THEME_TAG_ERR: "bold red"
}

_THEME_MAP: Dict[Verbosity, str] = {
    Verbosity.INFO: _THEME_TAG_INFO,
    Verbosity.INFO_VERBOSE: _THEME_TAG_INFO_VERBOSE,
    Verbosity.DEBUG: _THEME_TAG_DEBUG,
    Verbosity.DEBUG_VERBOSE: _THEME_TAG_DEBUG_VERBOSE
}


def _wrap_exception(exception_value: BaseException, /) -> OEError:

    if isinstance(exception_value, OEError):
        return exception_value

    if isinstance(exception_value, BaseException):
        oe_error = ErrInternal(
            "while leaving an officialeye context.",
            "An internal error occurred.",
        )
        oe_error.add_external_cause(exception_value)
        return oe_error

    return ErrInternal(
        "while determining the raised exception type.",
        "Could not decide how to handle the raised error."
    )


# noinspection PyProtectedMember
class _ChildrenListener:

    def __init__(self, terminal_ui, /):

        self._terminal_ui = terminal_ui

        self._progress = Progress(
            SpinnerColumn(),
            TextColumn("[progress.description]{task.description}"),
            console=self._terminal_ui._console,
            auto_refresh=True,
            disable=self._terminal_ui._verbosity == Verbosity.QUIET,
            transient=True
        )

        self._children: List[Tuple[InternalFeedbackInterface, TaskID, Connection]] = []
        self._children_lock = Lock()

        self._children_listener: Thread | None = None

    def listen_to(self, child: InternalFeedbackInterface, description: str, connection: Connection, /):

        # create a new task associated with the child
        task_id = self._progress.add_task(description)

        with self._children_lock:
            self._children.append((child, task_id, connection))

        if self._children_listener is None:
            # we have added the first child. therefore, the progress bar needs to be started.
            self._progress.start()

            # we need to also start a thread listening for messages from children
            def _child_listener():

                while True:

                    with self._children_lock:
                        if len(self._children) == 0:
                            break

                        connections: List[Connection] = [
                            c for _, _, c in self._children
                        ]

                    ready_connections = wait(connections)

                    for ready_connection in ready_connections:

                        message = ready_connection.recv()

                        if message[0] == IPCMessageType.CLOSE:
                            with (self._children_lock):
                                assert len(self._children) == 0, \
                                    "Close signal should be sent over IPC only when the children have already been disposed"

                        with self._children_lock:
                            for _, child_task_id, conn in self._children:
                                if conn == ready_connection:
                                    self._handle_message(message, child_task_id)

            self._children_listener = Thread(target=_child_listener)
            self._children_listener.start()

    def _handle_message(self, message: tuple, task_id: TaskID, /):

        message_type, args, kwargs = message

        if message_type == IPCMessageType.ECHO:
            self._terminal_ui.echo(*args, **kwargs)
        elif message_type == IPCMessageType.INFO:
            self._terminal_ui.info(*args, **kwargs)
        elif message_type == IPCMessageType.WARN:
            self._terminal_ui.warn(*args, **kwargs)
        elif message_type == IPCMessageType.ERROR:
            self._terminal_ui.error(*args, **kwargs)
        elif message_type == IPCMessageType.UPDATE_PROGRESS:
            self._progress.update(task_id, **kwargs)
        else:
            assert False, "Unknown IPC message type received by parent process."

    def stop_listening_to(self, child: InternalFeedbackInterface, /):

        with self._children_lock:
            cur_child = None
            task_id = None
            i = None

            for i, (cur_child, task_id, _) in enumerate(self._children):
                if cur_child == child:
                    break

            assert cur_child is not None, "The child to which we should stop listening, could not be found."
            assert task_id is not None
            assert i is not None

            self._children.pop(i)

            if len(self._children) == 0:
                # removed all children
                self._progress.stop()

    def dispose(self):

        with self._children_lock:
            while len(self._children) > 0:
                child, task_id, connection = self._children.pop()
                self._progress.remove_task(task_id)
                connection.close()
                child.dispose()

        if self._children_listener is not None:
            self._progress.stop()

            self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Joining the children listener thread.")

            self._children_listener.join()

            self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Children listener thread successfully joined.")


class TerminalUI(AbstractFeedbackInterface):

    def __init__(self, verbosity: Verbosity, /):
        super().__init__(verbosity)

        self._console = Console(highlight=False, theme=Theme(_THEME))
        self._err_console = Console(stderr=True, theme=Theme(_THEME))

        self._children_listener: _ChildrenListener = _ChildrenListener(self)

    def get_console(self) -> Console:
        return self._console

    def echo(self, verbosity: Verbosity, message: str | RichProtocol = "", /, *, err: bool = False, **kwargs: Any):

        assert verbosity != Verbosity.QUIET

        if self._verbosity < verbosity:
            return

        console = self._err_console if err else self._console

        if not console.is_interactive:
            kwargs.setdefault("crop", False)
            kwargs.setdefault("overflow", "ignore")

        console.print(message, **kwargs)

    def info(self, verbosity: Verbosity, message: str, /):
        assert verbosity != Verbosity.QUIET
        _tag = _THEME_MAP[verbosity]
        self.echo(verbosity, f"[{_tag}]INFO [/] {message}")

    def warn(self, verbosity: Verbosity, message: str, /):
        assert verbosity != Verbosity.QUIET
        self.echo(verbosity, f"[{_THEME_TAG_WARN}]WARN [/] {message}")

    def error(self, verbosity: Verbosity, message: str, /):
        assert verbosity != Verbosity.QUIET
        self.echo(verbosity, f"[{_THEME_TAG_ERR}]ERROR[/] {message}", err=True)

    def _print_oe_error(self, error: OEError, /, *, verbosity: Verbosity = Verbosity.INFO):

        self.error(verbosity, f"Error {error.code} ('{error.code_text}') occurred in module '{error.module}' {error.while_text}")
        self.error(verbosity, f"Problem: {error.problem_text}")

        error_details = error.get_details()

        if error_details is not None and verbosity != Verbosity.QUIET:
            detail_panel = Panel(error_details, title="Error details", expand=False, border_style="red", highlight=True)
            self._err_console.print(detail_panel)

        causes = error.get_causes()
        external_causes = error.get_external_causes()

        if len(causes) + len(external_causes) > 0:
            self._err_console.rule("The above error has been caused by the errors listed below")

        for cause in causes:
            self._print_oe_error(cause, verbosity=verbosity)

        for external_cause in external_causes:
            rich_traceback = Traceback.from_exception(external_cause.__class__, external_cause, None)
            self._err_console.print(rich_traceback)

    def handle_uncaught_error(self, exception_type: any, exception_value: BaseException, traceback: TracebackType, /):

        self._print_oe_error(_wrap_exception(exception_value))

        if self._verbosity >= Verbosity.DEBUG_VERBOSE:

            self._err_console.rule("Error details")

            rich_traceback = Traceback.from_exception(exception_type, exception_value, traceback)
            self._err_console.print(rich_traceback)

    def dispose(self):
        self._children_listener.dispose()

    def fork(self, description: str, /) -> AbstractFeedbackInterface:

        self.info(Verbosity.DEBUG_VERBOSE, "AbstractFeedbackInterface: fork()")

        rx, tx = Pipe(duplex=False)

        assert isinstance(rx, Connection)
        assert isinstance(tx, Connection)

        child = InternalFeedbackInterface(self._verbosity, tx)

        self._children_listener.listen_to(child, description, rx)

        return child

    def join(self, child: AbstractFeedbackInterface, future: Future, /):

        assert isinstance(child, InternalFeedbackInterface), "Invalid child type"

        self.info(Verbosity.DEBUG_VERBOSE, "AbstractFeedbackInterface: join()")

        self._children_listener.stop_listening_to(child)
