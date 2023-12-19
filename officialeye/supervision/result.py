from typing import Set

import numpy as np

from officialeye.match.result import KeypointMatchingResult


class SupervisionResult:

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, delta: np.ndarray, delta_prime: np.ndarray, transformation_matrix: np.ndarray, /):
        self.template_id = template_id
        self._kmr = kmr
        self._delta = delta
        self._delta_prime = delta_prime
        self._transformation_matrix = transformation_matrix

    def template_point_to_target_point(self, template_point: np.ndarray) -> np.ndarray:
        assert template_point.shape == (2,)
        assert self._delta.shape == (2,)
        assert self._delta_prime.shape == (2,)
        return (self._transformation_matrix @ (template_point - self._delta)) + self._delta_prime

    def get_relevant_keypoint_ids(self) -> Set[str]:
        rk = set()
        for match in self._kmr.get_matches():
            rk.add(match.get_keypoint().region_id)
        assert len(rk) > 0
        return rk

    def get_keypoint_matching_result(self) -> KeypointMatchingResult:
        return self._kmr

    def get_mse(self) -> float:
        error = 0.0
        for match in self._kmr.get_matches():
            s = match.get_original_template_point()
            # calculate prediction
            p = self.template_point_to_target_point(s)
            # calculate destination
            d = match.get_target_point()
            current_error = p - d
            error += np.dot(current_error, current_error)
        return error / self._kmr.get_total_match_count()
