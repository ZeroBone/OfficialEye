from officialeye.error.codes import ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND
from officialeye.error.error import ERR_MODULE_SUPERVISION, OEError


class ErrSupervision(OEError):

    def __init__(self, code_num: int, code_text: str, error_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_SUPERVISION, code_num, code_text, error_text, problem_text)


class ErrSupervisionCorrespondenceNotFound(ErrSupervision):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND[0], ERR_SUPERVISION_CORRESPONDENCE_NOT_FOUND[1], error_text, problem_text)
