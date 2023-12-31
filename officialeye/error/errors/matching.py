from officialeye.error.codes import ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS, ERR_MATCHING_INVALID_ENGINE_CONFIG
from officialeye.error.error import OEError, ERR_MODULE_MATCHING


class ErrMatching(OEError):

    def __init__(self, code: int, code_text: str, while_text: str, problem_text: str, /, *, is_regular: bool):
        super().__init__(ERR_MODULE_MATCHING, code, code_text, while_text, problem_text, is_regular=is_regular)


class ErrMatchingMatchCountOutOfBounds(ErrMatching):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS[0], ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS[1], while_text, problem_text, is_regular=True)


class ErrMatchingInvalidEngineConfig(ErrMatching):
    def __init__(self, while_text: str, problem_text: str, /):
        super().__init__(
            ERR_MATCHING_INVALID_ENGINE_CONFIG[0], ERR_MATCHING_INVALID_ENGINE_CONFIG[1], while_text, problem_text, is_regular=False)
