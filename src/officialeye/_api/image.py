from officialeye._api.context import Context


class Image:

    def __init__(self, context: Context, /, *, path: str):
        self._context = context

        self._path = path
