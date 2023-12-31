from officialeye.error.codes import ERR_TEMPLATE_INVALID_KEYPOINT, ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE, ERR_TEMPLATE_INVALID_MATCHING_ENGINE, \
    ERR_TEMPLATE_ID_NOT_UNIQUE, ERR_TEMPLATE_INVALID_FEATURE, ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG
from officialeye.error.error import OEError, ERR_MODULE_TEMPLATE


class ErrTemplate(OEError):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool = False):
        super().__init__(ERR_MODULE_TEMPLATE, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrTemplateInvalidSupervisionEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[0], ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[1], while_text, problem_text)


class ErrTemplateInvalidMatchingEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_MATCHING_ENGINE[0], ERR_TEMPLATE_INVALID_MATCHING_ENGINE[1], while_text, problem_text)


class ErrTemplateIdNotUnique(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_ID_NOT_UNIQUE[0], ERR_TEMPLATE_ID_NOT_UNIQUE[1], while_text, problem_text)


class ErrTemplateInvalidKeypoint(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_KEYPOINT[0], ERR_TEMPLATE_INVALID_KEYPOINT[1], while_text, problem_text)


class ErrTemplateInvalidFeature(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_FEATURE[0], ERR_TEMPLATE_INVALID_FEATURE[1], while_text, problem_text)


class ErrTemplateInvalidConcurrencyConfig(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[0], ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[1], while_text, problem_text)
