from __future__ import annotations

from concurrent.futures import ALL_COMPLETED
from concurrent.futures import Future as PythonFuture
from concurrent.futures import wait as python_wait
from typing import TYPE_CHECKING, Any, Dict, Iterable, Set, Tuple

# noinspection PyProtectedMember
from officialeye._internal.api_implementation import IApiInterfaceImplementation

# noinspection PyProtectedMember
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface

if TYPE_CHECKING:
    from officialeye._api.context import Context


class Future:

    def __init__(self, context: Context, python_future: PythonFuture, /, *, afi_fork: AbstractFeedbackInterface):
        self._context = context
        self._future = python_future
        self._afi_fork = afi_fork

        self._afi_joined = False

    def cancel(self) -> bool:
        """
        Attempt to cancel the call.
        If the call is currently being executed and cannot be canceled, then the method will return False,
        otherwise the call will be canceled, and the method will return True.
        """
        return self._future.cancel()

    def cancelled(self) -> bool:
        """ Return True if the call was successfully canceled. """
        return self._future.cancelled()

    def running(self) -> bool:
        """ Return True if the call is currently being executed and cannot be canceled. """
        return self._future.running()

    def done(self) -> bool:
        """ Return True if the call was successfully canceled or finished running. """
        return self._future.done()

    def _afi_join(self):
        if not self._afi_joined:
            self._afi_joined = True
            # noinspection PyProtectedMember
            self._context._get_afi().join(self._afi_fork, self._future)

    def result(self, timeout: float | None = None) -> Any:
        """
        Return the value returned by the call. If the call hasn’t yet completed, then this method will wait up to timeout seconds.
        If the call hasn’t completed in timeout seconds, then a TimeoutError will be raised. Timeout can be an int or float.
        If timeout is not specified or None, there is no limit to the wait time.

        If the future is canceled before completing, then CancelledError will be raised.

        If the call raised, this method will raise the same exception.
        """

        result = self._future.result(timeout=timeout)

        assert isinstance(result, IApiInterfaceImplementation), \
            "Every call to an internal API function should return a proper public API interface implementation"

        result.set_api_context(self._context)

        self._afi_join()

        return result

    def exception(self, timeout: float | None = None) -> Any:
        """
        Return the exception raised by the call.
        If the call hasn’t yet completed, then this method will wait up to timeout seconds.
        If the call hasn’t completed in timeout seconds, then a TimeoutError will be raised.
        Timeout can be an int or float.
        If timeout is not specified or None, there is no limit to the wait time.

        If the future is canceled before completing, then CancelledError will be raised.

        If the call completed without raising, None is returned.
        """

        err = self._future.exception(timeout=timeout)

        self._afi_join()

        return err


def wait(futures: Iterable[Future], /, *, timeout: float | None = None, return_when=ALL_COMPLETED) -> Tuple[Set[Future], Set[Future]]:

    # noinspection PyProtectedMember
    python_futures = (f._future for f in futures)

    original_futures: Dict[PythonFuture, Future] = {}

    for future in futures:
        # noinspection PyProtectedMember
        original_futures[future._future] = future

    done, not_done = python_wait(python_futures, timeout=timeout, return_when=return_when)

    corresponding_done = set((original_futures[d] for d in done))
    corresponding_not_done = set((original_futures[d] for d in not_done))

    return corresponding_done, corresponding_not_done
