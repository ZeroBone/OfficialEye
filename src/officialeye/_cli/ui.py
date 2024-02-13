from __future__ import annotations

from concurrent.futures import Future
from contextlib import contextmanager
from multiprocessing import Pipe

# noinspection PyProtectedMember
from multiprocessing.connection import Connection, wait
from threading import Lock, Thread
from types import TracebackType
from typing import Any, Dict, List, Set, Tuple

from rich.console import Console, ConsoleRenderable
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TaskID, TextColumn
from rich.theme import Theme
from rich.traceback import Traceback

# noinspection PyProtectedMember
from officialeye._internal.context.feedback import InternalFeedbackInterface, IPCMessageType

# noinspection PyProtectedMember
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye.error.error import OEError
from officialeye.error.errors.general import ErrOperationNotSupported
from officialeye.error.errors.internal import ErrInternal

_THEME_TAG_INFO = "info"
_THEME_TAG_INFO_VERBOSE = "infov"
_THEME_TAG_DEBUG = "debug"
_THEME_TAG_DEBUG_VERBOSE = "debugv"

_THEME_TAG_WARN = "warn"
_THEME_TAG_ERR = "err"

_THEME: Dict[str, str] = {
    _THEME_TAG_INFO: "bold green",
    _THEME_TAG_INFO_VERBOSE: "bold cyan",
    _THEME_TAG_DEBUG: "bold blue",
    _THEME_TAG_DEBUG_VERBOSE: "bold purple",
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
            "while leaving the CLI context.",
            "An internal error occurred.",
        )
        oe_error.add_external_cause(exception_value)
        return oe_error

    return ErrInternal(
        "while determining the raised exception type.",
        "Could not decide how to handle the raised error."
    )


def _child_listener(listener: _ChildrenListener, /):

    # a known child is a child that the listener thread is either already activaly listening to, or has already stopped listening to due to
    # the receival of a message over IPC, indicating that the child is done with the work
    known_children: Set[int] = set()

    while True:

        # first, we wait for one of the children to send some message
        with listener.children_lock:
            if len(listener.children) == 0:
                break

            # determine whether there are children the children listener thread does not know about
            # in this case, those children should be found and added to the known list,
            # and the corresponding lock should be acquired, indicating that the connection with the current
            # child has not yet been shut down gracefully
            for child_id in listener.children:

                if child_id in known_children:
                    continue

                child = listener.children[child_id]

                # indicate that we are listening to that child, and that once it is done with its work,
                # our handling of messages that might still be pending on the IPC, is to be respected
                child.is_being_listened_to.acquire()

                # now we know the child
                known_children.add(child_id)

            connections = [
                listener.child_listener_thread_rx,
                *(listener.children[child_id].connection for child_id in listener.children)
            ]

            assert len(connections) >= 1

        wait(connections, timeout=4.0)

        messages_to_handle: List[Tuple[Any, _Child]] = []

        with listener.children_lock:
            if len(listener.children) == 0:
                break

            for child_id in listener.children:
                child = listener.children[child_id]

                if not child.connection.poll():
                    continue

                message = child.connection.recv()

                messages_to_handle.append((message, child))
                    
        for message, child in messages_to_handle:
            listener.handle_message(message, child)


class _Child:

    def __init__(self, child_id: int, task_id: TaskID, connection: Connection, /):
        self.child_id = child_id
        self.task_id = task_id
        self.connection = connection
        self.is_being_listened_to = Lock()


# noinspection PyProtectedMember
class _ChildrenListener:

    def __init__(self, terminal_ui, /):

        self._terminal_ui = terminal_ui

        self._progress = Progress(
            SpinnerColumn(),
            TextColumn("{task.description}"),
            TextColumn("[cyan]{task.fields[status]}"),
            console=self._terminal_ui._console,
            auto_refresh=True,
            disable=self._terminal_ui._verbosity == Verbosity.QUIET,
            transient=True
        )

        self.children: Dict[int, _Child] = {}
        self.children_lock = Lock()

        self.child_listener_thread_rx, self._child_listener_thread_tx = Pipe(duplex=False)

        self._children_listener: Thread | None = None

    def handle_message(self, message: tuple, child: _Child, /):

        message_type, args, kwargs = message

        is_task_done: bool = False

        with self._terminal_ui.as_author(child.child_id):
            if message_type == IPCMessageType.ECHO:
                self._terminal_ui.echo(*args, **kwargs)
            elif message_type == IPCMessageType.INFO:
                self._terminal_ui.info(*args, **kwargs)
            elif message_type == IPCMessageType.WARN:
                self._terminal_ui.warn(*args, **kwargs)
            elif message_type == IPCMessageType.ERROR:
                self._terminal_ui.error(*args, **kwargs)
            elif message_type == IPCMessageType.UPDATE_STATUS:
                new_status_text: str = args[0]
                assert isinstance(new_status_text, str)
                self._progress.update(child.task_id, status=new_status_text)
            elif message_type == IPCMessageType.TASK_DONE:
                is_task_done = True
            else:
                raise AssertionError("Unknown IPC message type received by parent process.")

        if is_task_done:

            task_done_successfully: bool = args[0]
            assert isinstance(task_done_successfully, bool)

            self._terminal_ui.info(
                Verbosity.DEBUG,
                f"Child has indicated that the task is done (success={task_done_successfully}), "
                "releasing the corresponding lock to enable graceful shutdown of the child listener."
            )

            if task_done_successfully:
                self._progress.update(child.task_id, completed=100, status="[green]:heavy_check_mark: Success![/]")
            else:
                self._progress.update(child.task_id, completed=100, status="[red]:heavy_multiplication_x: Error![/]")

            child.is_being_listened_to.release()

    def listen_to(self, child_id: int, connection: Connection, description: str, /):

        # create a new task associated with the child
        task_id = self._progress.add_task(description, status="")

        with self.children_lock:
            assert child_id not in self.children, "Child ID is not unique."
            self.children[child_id] = _Child(child_id, task_id, connection)

        if self._children_listener is None:
            # we have added the first child. therefore, the progress bar needs to be started.
            self._progress.start()

            # we need to also start a thread listening for messages from children
            self._children_listener = Thread(target=_child_listener, name="Child Process Listener", args=(self,))
            self._children_listener.start()

    def stop_listening_to(self, child_id: int, /):

        # we first attempt to wait until the child listener thread has done processing all messages sent by the child
        # in other words we want to try and gracefully stop listening to the child

        with self.children_lock:

            if child_id not in self.children:
                self._terminal_ui.warn(
                    Verbosity.DEBUG,
                    f"Could not stop listening for child {child_id} because it could not be found among children the main process is listening to."
                )
                return

            _child = self.children[child_id]

            self._terminal_ui.info(
                Verbosity.DEBUG,
                f"Waiting for all messages from child {child_id} to be processed by the child listener thread."
            )

            child_lock = _child.is_being_listened_to

        if child_lock.acquire(blocking=True, timeout=4):
            child_lock.release()

            self._terminal_ui.info(
                Verbosity.DEBUG,
                f"The child listener thread indicated that it has processed all messages from child {child_id}."
            )
        else:
            self._terminal_ui.warn(
                Verbosity.DEBUG,
                f"The child listener thread did not indicate that it has processed all messages from child {child_id}!"
            )

        # we now proceed with removing the child completely

        last_child_removed = False

        with self.children_lock:

            if child_id not in self.children:
                self._terminal_ui.warn(
                    Verbosity.DEBUG,
                    f"Could not stop listening for child {child_id} because it could not be found among children the main process is listening to."
                )
                return

            child = self.children[child_id]

            child.connection.close()

            del self.children[child_id]

            if len(self.children) == 0:
                # we have removed the last child
                last_child_removed = True

        # notify the child listener thread that it is necessary to update the list of children
        # if we don't send this, then the child listener will be stuck waiting for a closed connection to send a message,
        # which will cause the child listener thread to sleep until the timeout of the wait expires, meaning that it will
        # cause significant lag to the user since we are synchronously joining the thread below
        # using this method of signalling the removal of the child above to the child listener thread, we fully circumvent this lag
        self._child_listener_thread_tx.send(())

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

    def remove_all_children(self):

        while True:

            with self.children_lock:
                children_to_be_removed = list(self.children.keys())

            if len(children_to_be_removed) == 0:
                break

            for child_id in children_to_be_removed:
                self.stop_listening_to(child_id)

    def dispose(self):
        self._terminal_ui.info(Verbosity.DEBUG_VERBOSE, "Dispoing child listener...")
        self.remove_all_children()


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

    def echo(self, verbosity: Verbosity, message: str | ConsoleRenderable = "", /, *, err: bool = False, **kwargs: Any) -> None:

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

    def info(self, verbosity: Verbosity, message: str, /) -> None:
        assert verbosity != Verbosity.QUIET
        _tag = _THEME_MAP[verbosity]
        self.echo(verbosity, f"[{_tag}]INFO [/] {message}", highlight=True)

    def warn(self, verbosity: Verbosity, message: str, /) -> None:
        assert verbosity != Verbosity.QUIET
        self.echo(verbosity, f"[{_THEME_TAG_WARN}]WARN [/] {message}")

    def error(self, verbosity: Verbosity, message: str, /) -> None:
        assert verbosity != Verbosity.QUIET
        self.echo(verbosity, f"[{_THEME_TAG_ERR}]ERROR[/] {message}", err=True)

    def update_status(self, new_status_text: str, /) -> None:
        raise ErrOperationNotSupported(
            "while updating status of a task.",
            "The terminal UI does not support this operation."
        )

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

        # remove all children to make sure that the progress bar dissapears and
        # does not interfere with the printing of the error to the terminal
        self._children_listener.remove_all_children()

        self._print_oe_error(_wrap_exception(exception_value))

        if self._verbosity >= Verbosity.DEBUG_VERBOSE:
            # self._err_console.rule("Error details")
            rich_traceback = Traceback.from_exception(exception_type, exception_value, traceback)
            self._err_console.print(rich_traceback)

    def dispose(self, exception_type: any = None, exception_value: BaseException | None = None, traceback: TracebackType | None = None) -> None:
        self._children_listener.dispose()

    def fork(self, description: str, /) -> AbstractFeedbackInterface:

        self.info(Verbosity.DEBUG_VERBOSE, "AbstractFeedbackInterface: fork()")

        rx, tx = Pipe(duplex=False)

        self._fork_counter += 1
        child_id = self._fork_counter

        child = InternalFeedbackInterface(self._verbosity, child_id, tx)

        self._children_listener.listen_to(child_id, rx, description)

        return child

    def join(self, child: AbstractFeedbackInterface, future: Future, /) -> None:

        assert isinstance(child, InternalFeedbackInterface), "Invalid child type"

        child_id = child.get_child_id()

        self.info(Verbosity.DEBUG_VERBOSE, f"AbstractFeedbackInterface: join() of child #{child_id}")

        self._children_listener.stop_listening_to(child_id)
