from typing import Dict

# noinspection PyPackageRequirements
import z3

from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult


class Election:

    def __init__(self, kmr: KeypointMatchingResult, /):
        self._kmr = kmr

    def run(self):

        # keys: matches (instances of Match)
        # values: z3 integer variables representing how many votes there are for the specified match
        match_votes: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.matches():
            match_votes[match] = z3.Int(f"votes_{match.get_debug_identifier()}")

        votes_are_nonnegative = z3.And(*(match_votes[match] >= 0 for match in self._kmr.matches()))

        solver = z3.Solver()
        solver.add(votes_are_nonnegative)
        result = solver.check()
        print(result)
        if result == z3.sat:
            print(solver.model())

    def get_result(self):
        pass
