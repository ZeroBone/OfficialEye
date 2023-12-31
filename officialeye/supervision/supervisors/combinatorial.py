import random
from typing import List, Dict

import numpy as np
# noinspection PyPackageRequirements
import z3

from officialeye.error.errors.supervision import ErrSupervisionInvalidEngineConfig
from officialeye.match.match import Match
from officialeye.match.result import KeypointMatchingResult
from officialeye.supervision.result import SupervisionResult
from officialeye.supervision.supervisor import Supervisor
from officialeye.util.logger import oe_warn, oe_debug


class CombinatorialSupervisor(Supervisor):

    ENGINE_ID = "combinatorial"

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__(CombinatorialSupervisor.ENGINE_ID, template_id, kmr)

        self._set_default_config({
            "min_match_factor": 0.1,
            "max_transformation_error": 5
        })

        self._z3_context = z3.Context()

        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("a", ctx=self._z3_context), z3.Real("b", ctx=self._z3_context)],
            [z3.Real("c", ctx=self._z3_context), z3.Real("d", ctx=self._z3_context)]
        ], dtype=z3.AstRef)

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match,
        # i.e. how consistent the match is with the affine transformation model
        self._match_weight: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_weight[match] = z3.Real(f"w_{match.get_debug_identifier()}", ctx=self._z3_context)

        _config_min_match_factor = self.get_config()["min_match_factor"]
        oe_debug(f"Min match factor: {_config_min_match_factor}")

        if _config_min_match_factor > 1.0:
            raise ErrSupervisionInvalidEngineConfig(
                f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                f"The `min_match_factor` value ({_config_min_match_factor}) cannot exceed 1.0."
            )

        if _config_min_match_factor < 0.0:
            raise ErrSupervisionInvalidEngineConfig(
                f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                f"The `min_match_factor` value ({_config_min_match_factor}) cannot be negative."
            )

        self._minimum_weight_to_enforce = self._kmr.get_total_match_count() * _config_min_match_factor

        _config_max_transformation_error = self.get_config()["max_transformation_error"]

        if _config_max_transformation_error < 0:
            raise ErrSupervisionInvalidEngineConfig(
                f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                f"The `max_transformation_error` value ({_config_max_transformation_error}) cannot be negative."
            )

        if _config_max_transformation_error > 5000:
            raise ErrSupervisionInvalidEngineConfig(
                f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                f"The `max_transformation_error` value ({_config_max_transformation_error}) is too high."
            )

        self._max_transformation_error = _config_max_transformation_error

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
            translated_template_point_x - target_point_x <= self._max_transformation_error,
            target_point_x - translated_template_point_x <= self._max_transformation_error,
            translated_template_point_y - target_point_y <= self._max_transformation_error,
            target_point_y - translated_template_point_y <= self._max_transformation_error,
        )

    def _run(self) -> List[SupervisionResult]:

        _results = []

        weights_lower_bounds = z3.And(*(self._match_weight[match] >= 0 for match in self._kmr.get_matches()), self._z3_context)
        weights_upper_bounds = z3.And(*(self._match_weight[match] <= 1 for match in self._kmr.get_matches()), self._z3_context)

        total_weight = z3.Sum(*(self._match_weight[match] for match in self._kmr.get_matches()))

        solver = z3.Optimize(ctx=self._z3_context)
        # TODO: make the timeout configurable
        solver.set("timeout", 2500)

        solver.add(weights_lower_bounds)
        solver.add(weights_upper_bounds)
        solver.add(total_weight >= self._minimum_weight_to_enforce)

        solver.maximize(total_weight)

        for keypoint_id in self._kmr.get_keypoint_ids():
            keypoint_matches = list(self._kmr.matches_for_keypoint(keypoint_id))

            if len(keypoint_matches) == 0:
                continue

            anchor_match = keypoint_matches[random.randint(0, len(keypoint_matches) - 1)]

            delta = anchor_match.get_original_template_point()
            delta_prime = anchor_match.get_target_point()

            solver.push()

            for match in self._kmr.get_matches():
                solver.add(z3.Implies(
                    self._match_weight[match] > 0,
                    # consistency check
                    self._get_consistency_check(match, delta, delta_prime),
                    ctx=self._z3_context
                ))

            result = solver.check()

            # print(solver.statistics())
            # print(solver.sexpr())

            if result == z3.unsat:
                oe_warn("Could not satisfy the imposed constraints.", fg="red")
                solver.pop()
                continue

            if result == z3.unknown:
                oe_warn("Could not decide the satifiability of the imposed constraints.", fg="red")
                solver.pop()
                continue

            assert result == z3.sat

            model = solver.model()
            model_evaluator = np.vectorize(lambda var: float(model.eval(var, model_completion=True).as_fraction()))

            # extract total weight and maximization target from model
            model_total_weight = model_evaluator(total_weight)

            # extract transformation matrix from model
            transformation_matrix = model_evaluator(self._transformation_matrix)

            _result = SupervisionResult(self.template_id, self._kmr, delta, delta_prime, transformation_matrix)
            # add fixed constant to make sure that the score value is always non-negative
            _result.set_score(model_total_weight)

            for match in self._kmr.get_matches():
                match_weight = model_evaluator(self._match_weight[match])
                _result.set_match_weight(match, match_weight)

            oe_debug(f"Error: {_result.get_weighted_mse()} "
                     f"Total weight and score: {model_total_weight}")

            _results.append(_result)

            solver.pop()

        return _results
