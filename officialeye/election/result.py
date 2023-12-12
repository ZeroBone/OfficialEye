from typing import List, Tuple, Set

import numpy as np

from officialeye.match.match import Match


class ElectionResult:

    def __init__(self, template_id: str, offset_vec: np.ndarray, transformation_matrix: np.ndarray):
        self.template_id = template_id
        self.offset_vec = offset_vec
        self.transformation_matrix = transformation_matrix

        self._matches: List[Tuple[Match, int]] = []

    def add_match(self, match: Match, vote_count: int, /):
        self._matches.append((match, vote_count))

    def get_relevant_keypoint_ids(self) -> Set[str]:
        rk = set()
        for match, _ in self._matches:
            rk.add(match.get_keypoint().region_id)
        return rk

    def get_matches(self) -> List[Tuple[Match, int]]:
        return self._matches
