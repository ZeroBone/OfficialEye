from officialeye.context import Context

_officialeye_context_ = Context()


def oe_context() -> Context:
    global _officialeye_context_
    return _officialeye_context_
