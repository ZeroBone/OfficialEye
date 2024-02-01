from __future__ import annotations

from concurrent.futures import Future
from contextlib import contextmanager
from multiprocessing import Pipe
# noinspection PyProtectedMember
from multiprocessing.connection import Connection, wait
from threading import Thread, Lock
from types import TracebackType
from typing import Any, TYPE_CHECKING, Dict, Tuple

from rich.console import Console
from rich.panel import Panel
from rich.theme import Theme
from rich.progress import Progress, SpinnerColumn, TextColumn, TaskID
from rich.traceback import Traceback

# noinspection PyProtectedMember
from officialeye._internal.context.feedback import InternalFeedbackInterface, IPCMessageType
from officialeye.error.error import OEError
from officialeye.error.errors.internal import ErrInternal
# noinspection PyProtectedMember
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface
# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye._types import RichProtocol

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


def _child_listener(listener: _ChildrenListener, /):

    while True:

        # first, we wait for one of the children to send some message
        with listener.children_lock:
            if len(listener.children) == 0:
                break

            connections = [
                listener.children[child_id][1] for child_id in listener.children
            ]

            assert len(connections) >= 1

        wait(connections, timeout=1.0)

        with listener.children_lock:
            if len(listener.children) == 0:
                break

            for child_id in listener.children:
                task_id, connection = listener.children[child_id]

                if not connection.poll():
                    continue

                message = connection.recv()
                    
                listener.handle_message(message, child_id, task_id)


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

        self.children: Dict[int, Tuple[TaskID, Connection]] = {}
        self.children_lock = Lock()

        self._children_listener: Thread | None = None

    def handle_message(self, message: tuple, child_id: int, task_id: TaskID, /):

        message_type, args, kwargs = message

        with self._terminal_ui.as_author(child_id):
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

    def listen_to(self, child_id: int, connection: Connection, description: str, /):

        # create a new task associated with the child
        task_id = self._progress.add_task(description)

        with self.children_lock:
            assert child_id not in self.children, "Child ID is not unique."
            self.children[child_id] = task_id, connection

        if self._children_listener is None:
            # we have added the first child. therefore, the progress bar needs to be started.
            self._progress.start()

            # we need to also start a thread listening for messages from children
            self._children_listener = Thread(target=_child_listener, name="Child Listener", args=(self,))
            self._children_listener.start()

    def stop_listening_to(self, child_id: int, /):

        last_child_removed = False

        with self.children_lock:

            assert child_id in self.children, "Child could not be found"

            task_id, connection = self.children[child_id]

            # self._progress.remove_task(task_id)
            connection.close()

            del self.children[child_id]

            if len(self.children) == 0:
                # we have removed the last child
                last_child_removed = True

        if last_child_removed:
            self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Last child removed, stopping the child listener and the progress bar.")

            # stop the thread listening for messages from children
            if self._children_listener is not None:
                self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Joining the children listener thread.")

                self._children_listener.join()
                self._children_listener = None

                self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Children listener thread successfully joined.")

            # stop the progress bar
            self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Stopping the progress bar due to removal of last child.")
            self._progress.stop()
            self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Stopped the progress bar due to removal of last child.")

    def dispose(self):

        self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Dispoing child listener...")

        while True:

            with self.children_lock:
                children_to_be_removed = list(self.children.keys())

            if len(children_to_be_removed) == 0:
                break

            for child_id in children_to_be_removed:
                self.stop_listening_to(child_id)


class TerminalUI(AbstractFeedbackInterface):

    def __init__(self, verbosity: Verbosity, /):
        super().__init__(verbosity)

        self._console = Console(highlight=False, theme=Theme(_THEME))
        self._err_console = Console(stderr=True, theme=Theme(_THEME))

        self._children_listener: _ChildrenListener = _ChildrenListener(self)
        self._fork_counter: int = 0

        self._last_printed_message_author: int | None = None

    def get_console(self) -> Console:
        return self._console

    def _print_message_authors(self) -> bool:
        return self._verbosity >= Verbosity.DEBUG

    @contextmanager
    def as_author(self, author: int):

        print_authors = self._print_message_authors()

        if print_authors and self._last_printed_message_author != author:
            # the same author prints the message
            self._console.rule(f"Messages by worker #{author}")

        self._last_printed_message_author = None

        yield self

        if print_authors:
            self._last_printed_message_author = author

    def echo(self, verbosity: Verbosity, message: str | RichProtocol = "", /, *, err: bool = False, **kwargs: Any):

        assert verbosity != Verbosity.QUIET

        if self._last_printed_message_author is not None:
            self._console.rule("Messages by the main process")
            self._last_printed_message_author = None

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
        self.echo(verbosity, f"[{_tag}]INFO [/] {message}", highlight=True)

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
            # self._err_console.rule("Error details")
            rich_traceback = Traceback.from_exception(exception_type, exception_value, traceback)
            self._err_console.print(rich_traceback)

    def dispose(self):
        self._children_listener.dispose()

    def fork(self, description: str, /) -> AbstractFeedbackInterface:

        self.info(Verbosity.DEBUG_VERBOSE, "AbstractFeedbackInterface: fork()")

        rx, tx = Pipe(duplex=False)

        assert isinstance(rx, Connection)
        assert isinstance(tx, Connection)

        self._fork_counter += 1
        child_id = self._fork_counter

        child = InternalFeedbackInterface(self._verbosity, child_id, tx)

        self._children_listener.listen_to(child_id, rx, description)

        return child

    def join(self, child: AbstractFeedbackInterface, future: Future, /):

        assert isinstance(child, InternalFeedbackInterface), "Invalid child type"

        child_id = child.get_child_id()

        self.info(Verbosity.DEBUG_VERBOSE, f"AbstractFeedbackInterface: join() of child #{child_id}")

        self._children_listener.stop_listening_to(child_id)
