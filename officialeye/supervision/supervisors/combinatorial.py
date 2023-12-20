from typing import List, Dict

import click
import numpy as np
# noinspection PyPackageRequirements
import z3

from officialeye.context.singleton import oe_context
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult
from officialeye.supervision.result import SupervisionResult
from officialeye.supervision.supervisor import Supervisor


class CombinatorialSupervisor(Supervisor):

    ENGINE_ID = "combinatorial"

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__(template_id, kmr)

        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("a"), z3.Real("b")],
            [z3.Real("c"), z3.Real("d")]
        ], dtype=z3.AstRef)

        self._transformation_error_bound = z3.Real("err_bound")

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match, i.e. how consistent the match is with the affine transformation model
        self._match_weight: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_weight[match] = z3.Real(f"w_{match.get_debug_identifier()}")

        self._minimum_weight_to_enforce = self._kmr.get_total_match_count() * 0.1
        self._max_transformation_error = 20

    def _get_consistency_check(self, match: Match, delta: np.ndarray, delta_prime: np.ndarray, transformation_error_max: int, /) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold
        In other words, targetpoint = M * (templatepoint - offset), where offset is a vector and M is a 2x2 matrix
        """

        assert transformation_error_max >= 0

        template_point = match.get_original_template_point()

        assert delta.shape == (2,)
        assert delta_prime.shape == (2,)
        assert template_point.shape == (2,)

        translated_template_point = self._transformation_matrix @ (template_point - delta) + delta_prime
        translated_template_point_x, translated_template_point_y = translated_template_point

        target_point_x, target_point_y = match.get_target_point()

        return z3.And(
            translated_template_point_x - target_point_x <= transformation_error_max,
            target_point_x - translated_template_point_x <= transformation_error_max,
            translated_template_point_y - target_point_y <= transformation_error_max,
            target_point_y - translated_template_point_y <= transformation_error_max,
        )

    def _run(self) -> List[SupervisionResult]:

        _results = []

        weights_lower_bounds = z3.And(*(self._match_weight[match] >= 0 for match in self._kmr.get_matches()))
        weights_upper_bounds = z3.And(*(self._match_weight[match] <= 1 for match in self._kmr.get_matches()))
        transformation_error_bounds = z3.And(
            self._transformation_error_bound >= 0,
            self._transformation_error_bound <= self._max_transformation_error
        )

        total_weight = z3.Sum(*(self._match_weight[match] for match in self._kmr.get_matches()))

        solver = z3.Optimize()
        # TODO: make the timeout configurable
        solver.set("timeout", 30000)

        solver.add(weights_lower_bounds)
        solver.add(weights_upper_bounds)
        solver.add(transformation_error_bounds)
        solver.add(total_weight >= self._minimum_weight_to_enforce)

        # for every pixel of error, this amount of weight will get subtracted
        # in other words, how much weight does erroring by one pixel correspond to?
        balance_factor = 1

        solver.maximize(total_weight - balance_factor * self._transformation_error_bound)

        for anchor_match in self._kmr.get_matches():
            delta = anchor_match.get_original_template_point()
            delta_prime = anchor_match.get_target_point()

            solver.push()

            for match in self._kmr.get_matches():
                solver.add(z3.Implies(
                    self._match_weight[match] > 0,
                    # consistency check
                    self._get_consistency_check(match, delta, delta_prime, 5)
                ))

            result = solver.check()
            if result == z3.unsat:
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho("Warning! Z3 returned unsat.", fg="red")
                continue

            if result == z3.unknown:
                if self.in_debug_mode() and not oe_context().quiet_mode:
                    click.secho("Warning! Z3 returned unknown.", fg="red")
                continue

            assert result == z3.sat

            model = solver.model()
            model_evaluator = np.vectorize(lambda var: float(model.eval(var, model_completion=True).as_fraction()))

            # extract total weight from model
            model_total_weight = model_evaluator(total_weight)

            # extract upper bound on transformation error from model
            model_transformation_error_bound = model_evaluator(self._transformation_error_bound)

            # extract transformation matrix from model
            transformation_matrix = model_evaluator(self._transformation_matrix)

            # _result = SupervisionResult(self.template_id, self._kmr, delta.copy(), delta_prime.copy(), transformation_matrix)
            _result = SupervisionResult(self.template_id, self._kmr, delta, delta_prime, transformation_matrix)

            for match in self._kmr.get_matches():
                match_weight = model_evaluator(self._match_weight[match])
                _result.set_match_weight(match, match_weight)

            if self.in_debug_mode() and not oe_context().quiet_mode:
                click.secho(f"Error: {_result.get_mse()} "
                            f"Total weight: {model_total_weight} "
                            f"Maximum transformation error: {model_transformation_error_bound}", fg="yellow")

            _results.append(_result)

            solver.pop()
            break

        return _results
