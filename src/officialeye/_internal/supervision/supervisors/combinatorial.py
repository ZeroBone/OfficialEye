import random
from typing import Dict, Generator

import numpy as np
import z3

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.supervision import ErrSupervisionInvalidEngineConfig
from officialeye._internal.logger.singleton import get_logger
from officialeye._internal.matching.match import Match
from officialeye._internal.matching.result import MatchingResult
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.supervision.supervisor import Supervisor


class CombinatorialSupervisor(Supervisor):

    ENGINE_ID = "combinatorial"

    def __init__(self, context: Context, template_id: str, kmr: MatchingResult, /):
        super().__init__(context, CombinatorialSupervisor.ENGINE_ID, template_id, kmr)

        # setup configuration
        def _min_match_factor_preprocessor(v: any) -> float:

            v = float(v)

            if v > 1.0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                    f"The `min_match_factor` value ({v}) cannot exceed 1.0."
                )

            if v < 0.0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor",
                    f"The `min_match_factor` value ({v}) cannot be negative."
                )

            return v

        self.get_config().set_value_preprocessor("min_match_factor", _min_match_factor_preprocessor)

        def _max_transformation_error_preprocessor(v: any) -> int:

            v = int(v)

            if v < 0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor.",
                    f"The `max_transformation_error` value ({v}) cannot be negative."
                )

            if v > 5000:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor.",
                    f"The `max_transformation_error` value ({v}) is too high."
                )

            return v

        self.get_config().set_value_preprocessor("max_transformation_error", _max_transformation_error_preprocessor)

        def _z3_timeout_preprocessor(v: any) -> int:

            v = int(v)

            if v < 1:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.ENGINE_ID}' supervisor.",
                    f"The `z3_timeout` value ({v}) cannot be negative or zero."
                )

            return v

        self.get_config().set_value_preprocessor("z3_timeout", _z3_timeout_preprocessor)

        # initialize all engine-specific values
        self._z3_context = z3.Context()

        # create variables for components of the translation matrix
        self._transformation_matrix = np.array([
            [z3.Real("a", ctx=self._z3_context), z3.Real("b", ctx=self._z3_context)],
            [z3.Real("c", ctx=self._z3_context), z3.Real("d", ctx=self._z3_context)]
        ], dtype=z3.AstRef)

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match,
        # i.e., how consistent the match is with the affine transformation model
        self._match_weight: Dict[Match, z3.ArithRef] = {}

        for match in self._kmr.get_matches():
            self._match_weight[match] = z3.Real(f"w_{match.get_debug_identifier()}", ctx=self._z3_context)

        _config_min_match_factor = self.get_config().get("min_match_factor", default=0.1)
        get_logger().debug(f"Min match factor: {_config_min_match_factor}")

        self._minimum_weight_to_enforce = self._kmr.get_total_match_count() * _config_min_match_factor
        self._max_transformation_error = self.get_config().get("max_transformation_error")

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

    def _run(self) -> Generator[SupervisionResult, None, None]:

        weights_lower_bounds = z3.And(*(self._match_weight[match] >= 0 for match in self._kmr.get_matches()), self._z3_context)
        weights_upper_bounds = z3.And(*(self._match_weight[match] <= 1 for match in self._kmr.get_matches()), self._z3_context)

        total_weight = z3.Sum(*(self._match_weight[match] for match in self._kmr.get_matches()))

        solver = z3.Optimize(ctx=self._z3_context)
        solver.set("timeout", self.get_config().get("z3_timeout", default=2500))

        solver.add(weights_lower_bounds)
        solver.add(weights_upper_bounds)
        solver.add(total_weight >= self._minimum_weight_to_enforce)

        solver.maximize(total_weight)

        for keypoint_id in self._kmr.get_keypoint_ids():
            keypoint_matches = list(self._kmr.matches_for_keypoint(keypoint_id))

            if len(keypoint_matches) == 0:
                continue

            # TODO: think whether this is a good algorithm design decision, and improve it if not
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

            if result == z3.unsat:
                get_logger().warn("Could not satisfy the imposed constraints.", fg="red")
                solver.pop()
                continue

            if result == z3.unknown:
                get_logger().warn("Could not decide the satifiability of the imposed constraints.", fg="red")
                solver.pop()
                continue

            assert result == z3.sat

            model = solver.model()
            model_evaluator = np.vectorize(lambda var: model.eval(var, model_completion=True).as_fraction())

            # extract total weight and maximization target from the model
            model_total_weight = float(model_evaluator(total_weight))

            # extract transformation matrix from model
            transformation_matrix = model_evaluator(self._transformation_matrix)

            _result = SupervisionResult(self.template_id, self._kmr, delta, delta_prime, transformation_matrix)
            # add fixed constant to make sure that the score value is always non-negative
            _result.set_score(model_total_weight)

            for match in self._kmr.get_matches():
                match_weight = model_evaluator(self._match_weight[match])
                _result.set_match_weight(match, match_weight)

            get_logger().debug(f"Error: {_result.get_weighted_mse()} Total weight and score: {model_total_weight}")

            yield _result

            solver.pop()
