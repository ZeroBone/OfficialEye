from officialeye.api.context import Context


class Template:

    def __init__(self, context: Context, /, *, path: str):
        self._context = context
        self._path = path

