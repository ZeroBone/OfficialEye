from officialeye.error.codes import ERR_TEMPLATE_INVALID_KEYPOINT, ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE, ERR_TEMPLATE_INVALID_MATCHING_ENGINE, \
    ERR_TEMPLATE_ID_NOT_UNIQUE
from officialeye.error.error import OEError, ERR_MODULE_TEMPLATE


class ErrTemplate(OEError):

    def __init__(self, code_num: int, code_text: str, error_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_TEMPLATE, code_num, code_text, error_text, problem_text)


class ErrTemplateInvalidKeypoint(ErrTemplate):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_KEYPOINT[0], ERR_TEMPLATE_INVALID_KEYPOINT[1], error_text, problem_text)


class ErrTemplateInvalidSupervisionEngine(ErrTemplate):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[0], ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[1], error_text, problem_text)


class ErrTemplateInvalidMatchingEngine(ErrTemplate):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_MATCHING_ENGINE[0], ERR_TEMPLATE_INVALID_MATCHING_ENGINE[1], error_text, problem_text)


class ErrTemplateIdNotUnique(ErrTemplate):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_ID_NOT_UNIQUE[0], ERR_TEMPLATE_ID_NOT_UNIQUE[1], error_text, problem_text)
