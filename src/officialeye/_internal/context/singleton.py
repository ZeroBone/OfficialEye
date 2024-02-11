from officialeye._internal.context.context import InternalContext
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface

_internal_context: InternalContext = InternalContext()


def get_internal_context() -> InternalContext:
    global _internal_context
    return _internal_context


def get_internal_afi() -> AbstractFeedbackInterface:
    return get_internal_context().get_afi()
