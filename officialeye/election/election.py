from typing import Dict

# noinspection PyPackageRequirements
import z3
import numpy as np

from officialeye.debug.container import DebugContainer
from officialeye.debug.debuggable import Debuggable
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult


class Election(Debuggable):

    def __init__(self, kmr: KeypointMatchingResult, /, *, debug: DebugContainer = None):
        super().__init__(debug=debug)
        self._kmr = kmr
        self._debug = debug

        # create variables for components of the offset vector
        self._offset = np.array([[z3.Real("o_x"), z3.Real("o_y")]], dtype=z3.AstRef).T
        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("t_x_1"), z3.Real("t_x_2")],
            [z3.Real("t_y_1"), z3.Real("t_y_2")]
        ], dtype=z3.AstRef)

        # keys: matches (instances of Match)
        # values: z3 integer variables representing how many votes there are for the specified match
        self._match_votes: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_votes[match] = z3.Int(f"votes_{match.get_debug_identifier()}")

        # configuration
        self._max_deviation = 10
        self._min_votes = int(0.5 * self._kmr.get_total_match_count())
        self._min_votes = max(self._min_votes, 1)

        print("Min votes: %d" % self._min_votes)

    def _get_consistency_check(self, match: Match) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold
        In other words, targetpoint = M * (templatepoint - offset), where offset is a vector and M is a 2x2 matrix
        """

        template_point = np.array([match.get_template_point()]).T

        translated_template_point = self._transformation_matrix @ (template_point - self._offset)

        translated_template_point_x = translated_template_point[0][0]
        translated_template_point_y = translated_template_point[1][0]

        target_point_x, target_point_y = match.get_target_point()

        return z3.And(
            translated_template_point_x - target_point_x <= self._max_deviation,
            translated_template_point_x - target_point_x >= -self._max_deviation,
            translated_template_point_y - target_point_y <= self._max_deviation,
            translated_template_point_y - target_point_y >= -self._max_deviation,
        )

    def run(self):

        votes_lower_bounds = z3.And(*(self._match_votes[match] >= 0 for match in self._kmr.get_matches()))

        votes_upper_bounds = z3.And(*(self._match_votes[match] <= 1 for match in self._kmr.get_matches()))

        elected_implies_consistent = z3.And(*(
            z3.Implies(
                # receiving at least one vote means getting elected
                self._match_votes[match] >= 1,
                # consistency check
                self._get_consistency_check(match)
            ) for match in self._kmr.get_matches()
        ))

        total_votes_requirement = (z3.Sum(*(self._match_votes[match] for match in self._kmr.get_matches()))
                                   >= self._min_votes)

        """
        for match in self._kmr.matches():
            print(match.get_template_point(), match.get_target_point())
        """

        solver = z3.Solver()
        solver.add(votes_lower_bounds)
        solver.add(votes_upper_bounds)
        solver.add(elected_implies_consistent)
        solver.add(total_votes_requirement)

        # TODO: implement binary search

        result = solver.check()
        print(result)
        if result == z3.sat:
            print(solver.model())

    def get_result(self):
        pass
