from officialeye._internal.error.error import OEError
from officialeye._internal.error.codes import *
from officialeye._internal.error.modules import ERR_MODULE_TEMPLATE


class ErrTemplate(OEError):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool = False, **kwargs):
        super().__init__(ERR_MODULE_TEMPLATE, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrTemplateInvalidSupervisionEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[0], ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidMatchingEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_MATCHING_ENGINE[0], ERR_TEMPLATE_INVALID_MATCHING_ENGINE[1], while_text, problem_text, **kwargs)


class ErrTemplateIdNotUnique(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_ID_NOT_UNIQUE[0], ERR_TEMPLATE_ID_NOT_UNIQUE[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidKeypoint(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_KEYPOINT[0], ERR_TEMPLATE_INVALID_KEYPOINT[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidFeature(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_FEATURE[0], ERR_TEMPLATE_INVALID_FEATURE[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidConcurrencyConfig(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[0], ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidSyntax(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_SYNTAX[0], ERR_TEMPLATE_INVALID_SYNTAX[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidFeatureClass(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_FEATURE_CLASS[0], ERR_TEMPLATE_INVALID_FEATURE_CLASS[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidMutator(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_MUTATOR[0], ERR_TEMPLATE_INVALID_MUTATOR[1], while_text, problem_text, **kwargs)


class ErrTemplateInvalidInterpretation(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_INTERPRETATION[0], ERR_TEMPLATE_INVALID_INTERPRETATION[1], while_text, problem_text, **kwargs)
