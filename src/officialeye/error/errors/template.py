from abc import ABC

from officialeye.error.codes import (
    ERR_TEMPLATE_ID_NOT_UNIQUE,
    ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG,
    ERR_TEMPLATE_INVALID_FEATURE,
    ERR_TEMPLATE_INVALID_FEATURE_CLASS,
    ERR_TEMPLATE_INVALID_INTERPRETATION,
    ERR_TEMPLATE_INVALID_KEYPOINT,
    ERR_TEMPLATE_INVALID_MATCHING_ENGINE,
    ERR_TEMPLATE_INVALID_MUTATOR,
    ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE,
    ERR_TEMPLATE_INVALID_SYNTAX,
)
from officialeye.error.error import OEError
from officialeye.error.modules import ERR_MODULE_TEMPLATE


class ErrTemplate(OEError, ABC):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool = False, **kwargs):
        super().__init__(ERR_MODULE_TEMPLATE, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrTemplateInvalidSupervisionEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[0], ERR_TEMPLATE_INVALID_SUPERVISION_ENGINE[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidMatchingEngine(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_MATCHING_ENGINE[0], ERR_TEMPLATE_INVALID_MATCHING_ENGINE[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateIdNotUnique(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_ID_NOT_UNIQUE[0], ERR_TEMPLATE_ID_NOT_UNIQUE[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidKeypoint(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_KEYPOINT[0], ERR_TEMPLATE_INVALID_KEYPOINT[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidFeature(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_FEATURE[0], ERR_TEMPLATE_INVALID_FEATURE[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidConcurrencyConfig(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[0], ERR_TEMPLATE_INVALID_CONCURRENCY_CONFIG[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidSyntax(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, yml_error: str | None = None, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_SYNTAX[0], ERR_TEMPLATE_INVALID_SYNTAX[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, yml_error, *kwargs

        self.yml_error = yml_error

    def get_details(self) -> str | None:
        return self.yml_error

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidFeatureClass(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_FEATURE_CLASS[0], ERR_TEMPLATE_INVALID_FEATURE_CLASS[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidMutator(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_MUTATOR[0], ERR_TEMPLATE_INVALID_MUTATOR[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrTemplateInvalidInterpretation(ErrTemplate):
    def __init__(self, while_text: str, problem_text: str, /, **kwargs):
        super().__init__(
            ERR_TEMPLATE_INVALID_INTERPRETATION[0], ERR_TEMPLATE_INVALID_INTERPRETATION[1], while_text, problem_text, **kwargs)

        self._init_args = while_text, problem_text, *kwargs

    def __reduce__(self):
        return self.__class__, self._init_args
