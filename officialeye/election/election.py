import math

from typing import Dict

import click
import numpy as np
# noinspection PyPackageRequirements
import z3

from officialeye.context.singleton import oe_context
from officialeye.debug.container import DebugContainer
from officialeye.debug.debuggable import Debuggable
from officialeye.election.result import ElectionResult
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult


class Election(Debuggable):

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /, *,
                 debug: DebugContainer = None, min_vote_fraction: float = 0.05):
        super().__init__(debug=debug)

        assert min_vote_fraction <= 1.0
        assert min_vote_fraction >= 0.0

        self.template_id = template_id
        self._kmr = kmr
        self._result = None

        # create variables for components of the offset vector
        self._offset_vec = np.array([[z3.Real("o_x"), z3.Real("o_y")]], dtype=z3.AstRef).T
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
        self._min_votes_required = math.ceil(min_vote_fraction * self._kmr.get_total_match_count())
        self._min_votes_required = max(self._min_votes_required, 1)
        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Total match count: {self._kmr.get_total_match_count()}", fg="yellow")
            click.secho(f"Minimum votes required: {self._min_votes_required}", fg="yellow")

    def _get_consistency_check(self, match: Match, transformation_error_max: int, /) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold
        In other words, targetpoint = M * (templatepoint - offset), where offset is a vector and M is a 2x2 matrix
        """

        assert transformation_error_max >= 0

        template_point = np.array([match.get_original_template_point()]).T

        translated_template_point = self._transformation_matrix @ (template_point - self._offset_vec)

        translated_template_point_x = translated_template_point[0][0]
        translated_template_point_y = translated_template_point[1][0]

        target_point_x, target_point_y = match.get_target_point()

        return z3.And(
            translated_template_point_x - target_point_x <= transformation_error_max,
            translated_template_point_x - target_point_x >= -transformation_error_max,
            translated_template_point_y - target_point_y <= transformation_error_max,
            translated_template_point_y - target_point_y >= -transformation_error_max,
        )

    def _generate_election_implies_consistency_check(self, transformation_error_max: int, /):
        return z3.And(*(
            z3.Implies(
                # receiving at least one vote means getting elected
                self._match_votes[match] >= 1,
                # consistency check
                self._get_consistency_check(match, transformation_error_max)
            ) for match in self._kmr.get_matches()
        ))

    def run(self):

        votes_lower_bounds = z3.And(*(self._match_votes[match] >= 0 for match in self._kmr.get_matches()))

        votes_upper_bounds = z3.And(*(self._match_votes[match] <= 1 for match in self._kmr.get_matches()))

        total_votes = z3.Sum(*(self._match_votes[match] for match in self._kmr.get_matches()))

        solver = z3.Solver()
        solver.set("timeout", 500)
        solver.add(votes_lower_bounds)
        solver.add(votes_upper_bounds)

        # transformation error is the maximum offset (in pixels) between the match and match provided by the translation
        transformation_error_bound_min = 0
        transformation_error_bound_max = 0x80

        model = None
        # upper bound on transformation error, corresponding to the model
        model_transformation_error_bound = None

        while transformation_error_bound_min <= transformation_error_bound_max:

            model_found_in_current_iter = False

            transformation_error_bound_cur = (transformation_error_bound_min + transformation_error_bound_max) // 2

            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho(f"--- [New iteration of transformation error optimization cycle] ---", fg="yellow")
                click.secho(f"Current bound on transformation error: {transformation_error_bound_cur}", fg="yellow")

            elected_implies_consistent = self._generate_election_implies_consistency_check(transformation_error_bound_cur)

            solver.push()
            solver.add(elected_implies_consistent)

            total_votes_min = self._min_votes_required
            total_votes_max = self._kmr.get_total_match_count()

            while total_votes_min <= total_votes_max:
                # we try to enforce the following amounts of votes
                min_votes = (total_votes_min + total_votes_max) // 2

                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho(f"Trying to enforce {min_votes} votes. Bounds:"
                                f" [{total_votes_min}, {total_votes_max}]", fg="yellow")

                solver.push()
                solver.add(total_votes >= min_votes)

                result = solver.check()
                if result == z3.sat:
                    model = solver.model()
                    model_transformation_error_bound = transformation_error_bound_cur
                    model_found_in_current_iter = True
                    # try to increase the minimum vote count
                    model_vote_count_raw: z3.IntNumRef = model.eval(total_votes, model_completion=True)
                    model_vote_count = model_vote_count_raw.as_long()
                    assert model_vote_count >= min_votes
                    total_votes_min = model_vote_count + 1
                elif result == z3.unknown:
                    total_votes_max = min_votes - 1
                    if self.in_debug_mode() and not oe_context().quiet_mode:
                        click.secho("Warning! Z3 returned unknown.", fg="red")
                else:
                    assert result == z3.unsat
                    total_votes_max = min_votes - 1

                solver.pop()

            if model_found_in_current_iter:
                # good, try to improve the bound on the transformation error further
                # specifically, we decrease the upper bound
                transformation_error_bound_max = transformation_error_bound_cur - 1
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho(f"Strengthening the transformation error bound.", fg="green")
            else:
                transformation_error_bound_min = transformation_error_bound_cur + 1
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho(f"Weakening the transformation error bound.", fg="red")

            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho(f"--- [Transformation error optimization cycle finished] ---", fg="yellow")

            solver.pop()

        if model is not None:

            evaluator = np.vectorize(lambda var: float(model.eval(var, model_completion=True).as_fraction()))

            # extract offset vector from model
            offset_vec = evaluator(self._offset_vec)
            # extract transformation matrix from model
            transformation_matrix = evaluator(self._transformation_matrix)

            self._result = ElectionResult(self.template_id, offset_vec, transformation_matrix)

            # extract vote counts from model
            elected_matches_count = 0
            for match in self._kmr.get_matches():
                vote_count = model.eval(self._match_votes[match], model_completion=True).as_long()
                self._result.add_match(match, vote_count)
                if vote_count >= 1:
                    elected_matches_count += 1

            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho(f"Election system: --- [Result] ---", fg="yellow")
                click.secho(f"Matches elected: {elected_matches_count} "
                            f"({elected_matches_count / self._kmr.get_total_match_count() * 100}%)", fg="yellow")
                click.secho(f"Upper bound on transformation error (the lower the better): {model_transformation_error_bound}", fg="yellow")

    def get_result(self) -> ElectionResult:
        return self._result
