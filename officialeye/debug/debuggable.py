from officialeye.debug.container import DebugContainer


class Debuggable:

    def __init__(self, /, *, debug: DebugContainer = None):
        self._debug = debug

    def in_debug_mode(self, /) -> bool:
        return self._debug is not None

    def debug(self) -> DebugContainer:
        return self._debug
