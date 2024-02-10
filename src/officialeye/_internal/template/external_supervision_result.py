from typing import Dict

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch
# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult
# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult
from officialeye._internal.template.external_template import ExternalTemplate
from officialeye._internal.template.internal_supervision_result import InternalSupervisionResult
from officialeye._internal.template.matching_result import ExternalMatchingResult


class ExternalSupervisionResult(ISupervisionResult):

    def __init__(self, internal_supervision_result: InternalSupervisionResult, /):
        super().__init__()

        self._template = ExternalTemplate(internal_supervision_result.template)
        self._matching_result = ExternalMatchingResult(internal_supervision_result.matching_result, self._template)

        self._score = internal_supervision_result.score
        self._delta = internal_supervision_result.delta
        self._delta_prime = internal_supervision_result.delta_prime
        self._transformation_matrix = internal_supervision_result.transformation_matrix

        # noinspection PyProtectedMember
        self._match_weights: Dict[IMatch, float] = internal_supervision_result.get_match_weights()

    @property
    def template(self) -> ExternalTemplate:
        return self._template

    @property
    def matching_result(self) -> IMatchingResult:
        return self._matching_result

    @property
    def score(self) -> float:
        return self._score

    @property
    def delta(self) -> np.ndarray:
        return self._delta

    @property
    def delta_prime(self) -> np.ndarray:
        return self._delta_prime

    @property
    def transformation_matrix(self) -> np.ndarray:
        return self._transformation_matrix

    def get_match_weight(self, match: IMatch, /) -> float:

        if match in self._match_weights:
            return self._match_weights[match]

        return 1.0
