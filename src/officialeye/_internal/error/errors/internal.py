from typing import Union

from officialeye._internal.error.codes import ERR_INTERNAL
from officialeye._internal.error.error import OEError
from officialeye._internal.error.modules import ERR_MODULE_INTERNAL


class ErrInternal(OEError):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_INTERNAL, ERR_INTERNAL[0], ERR_INTERNAL[1], while_text, problem_text, is_regular=False)
