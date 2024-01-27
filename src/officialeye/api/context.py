"""
Module represeting the OfficialEye context.
"""
from officialeye.api.error.errors.internal import ErrInvalidState


class Context:

    def __init__(self):
        self._entered: bool = False
        self._disposed: bool = False

    def __enter__(self):

        if self._entered:
            raise ErrInvalidState(
                "while entering the api context.",
                "The context has already been entered, which is illegal state."
            )

        self._entered = True
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        assert self._entered
        self._entered = False

        if self._disposed:
            raise ErrInvalidState(
                "while leaving the api context.",
                "The resources have already been disposed."
            )

        self.dispose()

    def dispose(self):
        self._disposed = True
        pass

