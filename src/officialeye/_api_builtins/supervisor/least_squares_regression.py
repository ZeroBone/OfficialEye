from __future__ import annotations

from typing import TYPE_CHECKING, Iterable

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import SupervisionResult

# noinspection PyProtectedMember
from officialeye._api.template.supervisor import Supervisor

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate

if TYPE_CHECKING:
    from officialeye.types import ConfigDict

_IND_A = 0
_IND_B = 1
_IND_C = 2
_IND_D = 3


class LeastSquaresRegressionSupervisor(Supervisor):

    SUPERVISOR_ID = "least_squares_regression"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(LeastSquaresRegressionSupervisor.SUPERVISOR_ID, config_dict)

    def setup(self, template: ITemplate, matching_result: IMatchingResult, /) -> None:
        pass

    def supervise(self, template: ITemplate, matching_result: IMatchingResult, /) -> Iterable[SupervisionResult]:

        match_count = matching_result.get_total_match_count()

        for anchor_match in matching_result.get_all_matches():

            delta = anchor_match.template_point
            delta_prime = anchor_match.target_point

            matrix = np.zeros((match_count << 1, 4), dtype=np.float64)
            rhs = np.zeros(match_count << 1, dtype=np.float64)

            for i, match in enumerate(matching_result.get_all_matches()):
                first_constraint_id = i << 1
                second_constraint_id = first_constraint_id + 1

                s = match.template_point
                d = match.target_point

                matrix[first_constraint_id][_IND_A] = s[0] - delta[0]
                matrix[first_constraint_id][_IND_B] = s[1] - delta[1]
                rhs[first_constraint_id] = d[0] - delta_prime[0]

                matrix[second_constraint_id][_IND_C] = s[0] - delta[0]
                matrix[second_constraint_id][_IND_D] = s[1] - delta[1]
                rhs[second_constraint_id] = d[1] - delta_prime[1]

            regression_matrix = matrix.T @ matrix
            regression_matrix = np.linalg.inv(regression_matrix)
            rhs_applied = matrix.T @ rhs
            x = regression_matrix @ rhs_applied

            transformation_matrix = np.array([
                [x[_IND_A], x[_IND_B]],
                [x[_IND_C], x[_IND_D]]
            ])

            _result = SupervisionResult(
                delta=delta,
                delta_prime=delta_prime,
                transformation_matrix=transformation_matrix
            )

            yield _result
