from typing import Dict, Union

import click
import numpy as np
# noinspection PyPackageRequirements
import z3

from officialeye.context.singleton import oe_context
from officialeye.debug.container import DebugContainer
from officialeye.debug.debuggable import Debuggable
from officialeye.supervisor.result import SupervisionResult
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult


class Supervisor(Debuggable):

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /, *,
                 debug: DebugContainer = None):
        super().__init__(debug=debug)

        self.template_id = template_id
        self._kmr = kmr

        # create variables for components of the offset vector
        self._offset_vec = np.array([[z3.Real("o_x"), z3.Real("o_y")]], dtype=z3.AstRef).T
        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("t_x_1"), z3.Real("t_x_2")],
            [z3.Real("t_y_1"), z3.Real("t_y_2")]
        ], dtype=z3.AstRef)

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match, i.e. how consistent the match is with the affine transformation model
        self._match_error: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_error[match] = z3.Real(f"e_{match.get_debug_identifier()}")

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Total match count: {self._kmr.get_total_match_count()}", fg="yellow")

    def _get_consistency_check(self, match: Match, /) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold
        In other words, targetpoint = M * (templatepoint - offset), where offset is a vector and M is a 2x2 matrix
        """

        template_point = np.array([match.get_original_template_point()]).T

        translated_template_point = self._transformation_matrix @ (template_point - self._offset_vec)

        translated_template_point_x = translated_template_point[0][0]
        translated_template_point_y = translated_template_point[1][0]

        target_point_x, target_point_y = match.get_target_point()

        return z3.And(
            translated_template_point_x - target_point_x <= self._match_error[match],
            translated_template_point_x - target_point_x >= -self._match_error[match],
            translated_template_point_y - target_point_y <= self._match_error[match],
            translated_template_point_y - target_point_y >= -self._match_error[match],
        )

    def run(self) -> Union[SupervisionResult, None]:

        error_lower_bounds = z3.And(*(self._match_error[match] >= 0 for match in self._kmr.get_matches()))
        total_error = z3.Sum(*(self._match_error[match] for match in self._kmr.get_matches()))

        solver = z3.Optimize()
        solver.set("timeout", 30000)

        solver.add(error_lower_bounds)

        for match in self._kmr.get_matches():
            solver.add(self._get_consistency_check(match))

        solver.minimize(total_error)

        _result = solver.check()

        if _result == z3.unsat:
            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho("Warning! Z3 returned unsat.", fg="red")
            return None

        if _result == z3.unknown:
            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho("Warning! Z3 returned unknown.", fg="red")
            return None

        assert _result == z3.sat

        model = solver.model()

        evaluator = np.vectorize(lambda var: float(model.eval(var, model_completion=True).as_fraction()))

        # extract offset vector from model
        offset_vec = evaluator(self._offset_vec)
        # extract transformation matrix from model
        transformation_matrix = evaluator(self._transformation_matrix)

        _result = SupervisionResult(self.template_id, offset_vec, transformation_matrix)

        # extract vote counts from model
        matches_chosen_count = 0
        for match in self._kmr.get_matches():
            match_error = model.eval(self._match_error[match], model_completion=True).as_fraction()
            _result.add_match(match, match_error)
            if match_error <= 10:
                matches_chosen_count += 1

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Supervision system: --- [Result] ---", fg="yellow")
            click.secho(f"Matches chosen: {matches_chosen_count} "
                        f"({matches_chosen_count / self._kmr.get_total_match_count() * 100}%)", fg="yellow")

        return _result
