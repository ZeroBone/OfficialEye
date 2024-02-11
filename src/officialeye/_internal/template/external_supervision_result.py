from __future__ import annotations

from typing import Dict, TYPE_CHECKING

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.context import Context
# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch
# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult
from officialeye._internal.api_implementation import IApiInterfaceImplementation
from officialeye._internal.template.external_template import ExternalTemplate
from officialeye._internal.template.external_matching_result import ExternalMatchingResult


if TYPE_CHECKING:
    from officialeye._internal.template.internal_supervision_result import InternalSupervisionResult


class ExternalSupervisionResult(ISupervisionResult, IApiInterfaceImplementation):

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

    def set_api_context(self, context: Context, /):
        self._template.set_api_context(context)
        self._matching_result.set_api_context(context)

    @property
    def template(self) -> ExternalTemplate:
        return self._template

    @property
    def matching_result(self) -> ExternalMatchingResult:
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
