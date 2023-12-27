from officialeye.error.codes import ERR_IO_INVALID_SUPERVISION_ENGINE
from officialeye.error.error import OEError, ERR_MODULE_IO


class ErrIO(OEError):

    def __init__(self, code_num: int, code_text: str, error_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_IO, code_num, code_text, error_text, problem_text)


class ErrIOInvalidSupervisionEngine(ErrIO):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_IO_INVALID_SUPERVISION_ENGINE[0], ERR_IO_INVALID_SUPERVISION_ENGINE[1], error_text, problem_text)
