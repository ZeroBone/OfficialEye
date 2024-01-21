from officialeye._internal.error.error import OEError
from officialeye._internal.error.codes import ERR_IO_INVALID_SUPERVISION_ENGINE, ERR_IO_OPERATION_NOT_SUPPORTED_BY_DRIVER, ERR_IO_INVALID_PATH
from officialeye._internal.error.modules import ERR_MODULE_IO


class ErrIO(OEError):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool = False, **kwargs):
        super().__init__(ERR_MODULE_IO, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrIOInvalidSupervisionEngine(ErrIO):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_IO_INVALID_SUPERVISION_ENGINE[0], ERR_IO_INVALID_SUPERVISION_ENGINE[1], while_text, problem_text, **kwargs)


class ErrIOOperationNotSupportedByDriver(ErrIO):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_IO_OPERATION_NOT_SUPPORTED_BY_DRIVER[0], ERR_IO_OPERATION_NOT_SUPPORTED_BY_DRIVER[1], while_text, problem_text, **kwargs)


class ErrIOInvalidPath(ErrIO):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_IO_INVALID_PATH[0], ERR_IO_INVALID_PATH[1], while_text, problem_text, **kwargs)
