from typing import List, Tuple

import numpy as np

from officialeye.match.match import Match


class ElectionResult:

    def __init__(self, offset_vec: np.ndarray, transformation_matrix: np.ndarray):
        self.offset_vec = offset_vec
        self.transformation_matrix = transformation_matrix

        self._matches: List[Tuple[Match, int]] = []

    def add_match(self, match: Match, vote_count: int, /):
        self._matches.append((match, vote_count))
