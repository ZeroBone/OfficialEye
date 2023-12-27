from officialeye.error.codes import ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS
from officialeye.error.error import OEError, ERR_MODULE_MATCHING


class ErrMatching(OEError):

    def __init__(self, code_num: int, code_text: str, error_text: str, problem_text: str, /):
        super().__init__(ERR_MODULE_MATCHING, code_num, code_text, error_text, problem_text)


class ErrMatchingMatchCountOutOfBounds(ErrMatching):
    def __init__(self, error_text: str, problem_text: str, /):
        super().__init__(
            ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS[0], ERR_MATCHING_MATCH_COUNT_OUT_OF_BOUNDS[1], error_text, problem_text)
