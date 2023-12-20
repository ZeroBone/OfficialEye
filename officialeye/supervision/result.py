from typing import Set, Dict

import numpy as np

from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult


class SupervisionResult:

    def __init__(self, template_id: str, kmr: KeypointMatchingResult,
                 delta: np.ndarray, delta_prime: np.ndarray, transformation_matrix: np.ndarray, /):
        self.template_id = template_id
        self._kmr = kmr

        assert delta.shape == (2,)
        assert delta_prime.shape == (2,)
        assert transformation_matrix.shape == (2, 2)

        # offset in the template's coordinates
        self._delta = delta
        # offset in the target image's coordinates
        self._delta_prime = delta_prime
        self.dpo = delta_prime.copy()

        self._transformation_matrix = transformation_matrix

        # keys: matches
        # values: weights assigned by the supervision engine to each match (assigning is optional)
        # the higher the weight, the more we trust the correctness of the match and greater its individual impact should be
        # by default, the weight is 1
        self._match_weights: Dict[Match, float] = {}

    def get_match_weight(self, match: Match, /) -> float:
        if match in self._match_weights:
            return self._match_weights[match]
        return 1.0

    def set_match_weight(self, match: Match, weight: float, /):
        self._match_weights[match] = weight

    def template_point_to_target_point(self, template_point: np.ndarray, /) -> np.ndarray:
        assert template_point.shape == (2,)
        assert self._delta.shape == (2,)
        assert self._delta_prime.shape == (2,)
        return self._transformation_matrix @ (template_point - self._delta) + self._delta_prime

    def get_relevant_keypoint_ids(self) -> Set[str]:
        rk = set()
        for match in self._kmr.get_matches():
            rk.add(match.get_keypoint().region_id)
        assert len(rk) > 0
        return rk

    def get_keypoint_matching_result(self) -> KeypointMatchingResult:
        return self._kmr

    def get_mse(self, /, *, weighted: bool = True) -> float:
        error = 0.0
        for match in self._kmr.get_matches():
            s = match.get_original_template_point()
            # calculate prediction
            p = self.template_point_to_target_point(s)
            # calculate destination
            d = match.get_target_point()
            current_error = p - d
            current_error_value = np.dot(current_error, current_error)

            if weighted:
                error += current_error_value * self.get_match_weight(match)
            else:
                error += current_error_value

        return error / self._kmr.get_total_match_count()
