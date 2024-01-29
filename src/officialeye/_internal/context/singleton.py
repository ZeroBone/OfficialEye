from officialeye._api.feedback.abstract import AbstractFeedbackInterface
from officialeye._internal.context.context import InternalContext
from officialeye.error.errors.internal import ErrInvalidState

_internal_context: InternalContext | None = None


def initialize_internal_context(**kwargs):

    global _internal_context

    if _internal_context is not None:
        raise ErrInvalidState(
            "while initializing the internal context.",
            "The context seems to already have been initialized."
        )

    _internal_context = InternalContext(**kwargs)


def get_internal_context() -> InternalContext:
    global _internal_context

    if _internal_context is None:
        raise ErrInvalidState(
            "while accessing the internal context.",
            "The context has not been properly initialized."
        )

    return _internal_context


def get_internal_afi() -> AbstractFeedbackInterface:
    return get_internal_context().get_afi()
