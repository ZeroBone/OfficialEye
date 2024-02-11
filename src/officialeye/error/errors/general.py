from officialeye.error.codes import ERR_GENERAL
from officialeye.error.error import OEError
from officialeye.error.modules import ERR_MODULE_GENERAL


class ErrGeneral(OEError):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_GENERAL, ERR_GENERAL[0], ERR_GENERAL[1], while_text, problem_text, is_regular=False)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrOperationNotSupported(ErrGeneral):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(while_text, problem_text)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrInvalidKey(ErrGeneral):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(while_text, problem_text)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrInvalidIdentifier(ErrGeneral):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(while_text, problem_text)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrObjectNotInitialized(ErrGeneral):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(while_text, problem_text)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args


class ErrInvalidImage(ErrGeneral):

    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(while_text, problem_text)

        self._init_args = while_text, problem_text

    def __reduce__(self):
        return self.__class__, self._init_args
