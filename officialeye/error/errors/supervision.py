from officialeye.error.codes import ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND, ERR_SUPERVISION_INVALID_ENGINE_CONFIG
from officialeye.error.error import ERR_MODULE_SUPERVISION, OEError


class ErrSupervision(OEError):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool):
        super().__init__(ERR_MODULE_SUPERVISION, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrSupervisionCorrespondenceNotFound(ErrSupervision):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND[0], ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND[1], while_text, problem_text, is_regular=True)


class ErrSupervisionInvalidEngineConfig(ErrSupervision):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_SUPERVISION_INVALID_ENGINE_CONFIG[0], ERR_SUPERVISION_INVALID_ENGINE_CONFIG[1], while_text, problem_text, is_regular=False)
