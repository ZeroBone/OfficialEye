from __future__ import annotations

from typing import TYPE_CHECKING, Dict

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.future import Future

# noinspection PyProtectedMember
from officialeye._api.template.interpretation_result import IInterpretationResult

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult
from officialeye.error.errors.general import ErrOperationNotSupported

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.image import IImage

    # noinspection PyProtectedMember
    from officialeye._api.template.match import IMatch

    # noinspection PyProtectedMember
    from officialeye._api.template.supervision_result import SupervisionResult
    from officialeye._internal.template.internal_matching_result import InternalMatchingResult
    from officialeye._internal.template.internal_template import InternalTemplate


class InternalSupervisionResult(ISupervisionResult):

    def __init__(self, supervision_result: SupervisionResult, internal_template: InternalTemplate,
                 internal_matching_result: InternalMatchingResult, /):
        self._supervision_result = supervision_result
        self._internal_template = internal_template
        self._internal_matching_result = internal_matching_result

    @property
    def template(self) -> InternalTemplate:
        return self._internal_template

    @property
    def matching_result(self) -> InternalMatchingResult:
        return self._internal_matching_result

    @property
    def score(self) -> float:
        return self._supervision_result.get_score()

    @property
    def delta(self) -> np.ndarray:
        return self._supervision_result.delta

    @property
    def delta_prime(self) -> np.ndarray:
        return self._supervision_result.delta_prime

    @property
    def transformation_matrix(self) -> np.ndarray:
        return self._supervision_result.transformation_matrix

    def interpret_async(self, /, *, target: IImage) -> Future:
        raise ErrOperationNotSupported(
            "while accessing an internal supervision result instance.",
            "The way in which it was accessed is not supported."
        )

    def interpret(self, /, **kwargs) -> IInterpretationResult:
        raise ErrOperationNotSupported(
            "while accessing an internal supervision result instance.",
            "The way in which it was accessed is not supported."
        )

    def get_match_weights(self) -> Dict[IMatch, float]:
        # noinspection PyProtectedMember
        return self._supervision_result._match_weights

    def get_match_weight(self, match: IMatch, /) -> float:

        match_weights = self.get_match_weights()

        if match in match_weights:
            return match_weights[match]

        return 1.0
