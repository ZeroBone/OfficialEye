import sys
from typing import Set, Dict

import cv2
import numpy as np

from officialeye._internal.matching.match import Match
from officialeye._internal.matching.result import MatchingResult


class SupervisionResult:

    def __init__(self, template_id: str, kmr: MatchingResult,
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
        # self.dpo = delta_prime.copy()

        self._transformation_matrix = transformation_matrix

        # keys: matches
        # values: weights assigned by the supervision engine to each match (assigning is optional)
        # the higher the weight, the more we trust the correctness of the match and the greater its individual impact should be.
        # by default, the weight is 1.
        self._match_weights: Dict[Match, float] = {}

        # an optional value the supervision engine can set, representing how confident the engine is that the result is of high quality
        self._score = 0.0

    def get_score(self) -> float:
        assert self._score >= 0.0
        return self._score

    def set_score(self, new_score: float, /):
        assert new_score >= 0
        assert isinstance(new_score, float)
        self._score = new_score

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

    def get_feature_warped_region(self, target: cv2.Mat, feature) -> cv2.Mat:

        feature_tl = feature.get_top_left_vec()
        feature_tr = feature.get_top_right_vec()
        feature_bl = feature.get_bottom_left_vec()
        feature_br = feature.get_bottom_right_vec()

        target_tl = self.template_point_to_target_point(feature_tl)
        target_tr = self.template_point_to_target_point(feature_tr)
        target_bl = self.template_point_to_target_point(feature_bl)
        target_br = self.template_point_to_target_point(feature_br)

        dest_tl = np.array([0, 0], dtype=np.float64)
        dest_tr = np.array([feature.w, 0], dtype=np.float64)
        dest_br = np.array([feature.w, feature.h], dtype=np.float64)
        dest_bl = np.array([0, feature.h], dtype=np.float64)

        source_points = [target_tl, target_tr, target_br, target_bl]
        destination_points = [dest_tl, dest_tr, dest_br, dest_bl]

        homography = cv2.getPerspectiveTransform(np.float32(source_points), np.float32(destination_points))

        return cv2.warpPerspective(
            target,
            np.float32(homography),
            (feature.w, feature.h),
            flags=cv2.INTER_LINEAR
        )

    def get_relevant_keypoint_ids(self) -> Set[str]:
        rk = set()
        for match in self._kmr.get_matches():
            rk.add(match.get_keypoint().region_id)
        assert len(rk) > 0
        return rk

    def get_keypoint_matching_result(self) -> MatchingResult:
        return self._kmr

    def get_weighted_mse(self, /) -> float:
        error = 0.0
        singificant_match_count = 0
        for match in self._kmr.get_matches():

            match_weight = self.get_match_weight(match)

            if match_weight < sys.float_info.epsilon:
                continue

            singificant_match_count += 1

            s = match.get_original_template_point()
            # calculate prediction
            p = self.template_point_to_target_point(s)
            # calculate destination
            d = match.get_target_point()
            current_error = p - d
            current_error_value = np.dot(current_error, current_error)
            error += current_error_value * match_weight

        return error / singificant_match_count
