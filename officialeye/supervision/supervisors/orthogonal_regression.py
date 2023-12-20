from typing import Dict, List

import click
import numpy as np
# noinspection PyPackageRequirements
import z3

from officialeye.context.singleton import oe_context
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult

from officialeye.supervision.result import SupervisionResult
from officialeye.supervision.supervisor import Supervisor


class OrthogonalRegressionSupervisor(Supervisor):

    ENGINE_ID = "orthogonal_regression"

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__(template_id, kmr)

        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("a"), z3.Real("b")],
            [z3.Real("c"), z3.Real("d")]
        ], dtype=z3.AstRef)

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match, i.e. how consistent the match is with the affine transformation model
        self._match_error: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_error[match] = z3.Real(f"e_{match.get_debug_identifier()}")

    def _get_consistency_check(self, match: Match, delta: np.ndarray, delta_prime: np.ndarray, /) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold
        In other words, targetpoint = M * (templatepoint - offset), where offset is a vector and M is a 2x2 matrix
        """

        template_point = match.get_original_template_point()

        assert delta.shape == (2,)
        assert delta_prime.shape == (2,)
        assert template_point.shape == (2,)

        translated_template_point = self._transformation_matrix @ (template_point - delta) + delta_prime
        translated_template_point_x, translated_template_point_y = translated_template_point

        target_point_x, target_point_y = match.get_target_point()

        return z3.And(
            translated_template_point_x - target_point_x <= self._match_error[match],
            translated_template_point_x - target_point_x >= -self._match_error[match],
            translated_template_point_y - target_point_y <= self._match_error[match],
            translated_template_point_y - target_point_y >= -self._match_error[match],
        )

    def _run(self) -> List[SupervisionResult]:

        _results = []

        for anchor_match in self._kmr.get_matches():
            delta = anchor_match.get_original_template_point()
            delta_prime = anchor_match.get_target_point()

            error_lower_bounds = z3.And(*(self._match_error[match] >= 0 for match in self._kmr.get_matches()))
            total_error = z3.Sum(*(self._match_error[match] for match in self._kmr.get_matches()))

            solver = z3.Optimize()
            # TODO: make the timeout configurable
            solver.set("timeout", 30000)

            solver.add(error_lower_bounds)

            for match in self._kmr.get_matches():
                solver.add(self._get_consistency_check(match, delta, delta_prime))

            solver.minimize(total_error)

            _result = solver.check()

            if _result == z3.unsat:
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho("Warning! Z3 returned unsat.", fg="red")
                return []

            if _result == z3.unknown:
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho("Warning! Z3 returned unknown.", fg="red")
                return []

            assert _result == z3.sat

            model = solver.model()

            evaluator = np.vectorize(lambda var: float(model.eval(var, model_completion=True).as_fraction()))

            # extract transformation matrix from model
            transformation_matrix = evaluator(self._transformation_matrix)

            _result = SupervisionResult(self.template_id, self._kmr, delta, delta_prime, transformation_matrix)

            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho(f"Error: {_result.get_mse()}", fg="yellow")

            _results.append(_result)

        return _results
