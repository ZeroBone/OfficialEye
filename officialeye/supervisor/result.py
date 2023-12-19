from fractions import Fraction
from typing import List, Tuple, Set

import numpy as np

from officialeye.match.match import Match


class SupervisionResult:

    def __init__(self, template_id: str, offset_vec: np.ndarray, transformation_matrix: np.ndarray):
        self.template_id = template_id
        self._offset_vec = offset_vec
        self._transformation_matrix = transformation_matrix

        self._matches: List[Tuple[Match, Fraction]] = []

    def add_match(self, match: Match, weight: Fraction, /):
        self._matches.append((match, weight))

    def template_point_to_target_point(self, template_point: np.ndarray) -> np.ndarray:
        return self._transformation_matrix @ (template_point - self._offset_vec)

    def get_relevant_keypoint_ids(self) -> Set[str]:
        rk = set()
        for match, _ in self._matches:
            rk.add(match.get_keypoint().region_id)
        return rk

    def get_matches(self) -> List[Tuple[Match, Fraction]]:
        return self._matches
