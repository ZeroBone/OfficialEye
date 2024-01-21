from typing import Union

from officialeye.error.codes import ERR_INTERNAL
from officialeye.error.error import OEError
from officialeye.error.modules import ERR_MODULE_INTERNAL


class ErrInternal(OEError):

    def __init__(self, while_text: str, problem_text: str, /, *, external_cause: Union[BaseException, None] = None):
        super().__init__(ERR_MODULE_INTERNAL, ERR_INTERNAL[0], ERR_INTERNAL[1], while_text, problem_text, is_regular=False)

        self.external_cause = external_cause
