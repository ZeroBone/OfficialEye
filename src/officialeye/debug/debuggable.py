from officialeye.context.singleton import oe_context
from officialeye.debug.container import DebugContainer


class Debuggable:

    def __init__(self):
        if oe_context().debug_mode:
            self._debug = DebugContainer()
        else:
            self._debug = None

    def in_debug_mode(self, /) -> bool:
        return self._debug is not None

    def debug(self) -> DebugContainer:
        return self._debug
