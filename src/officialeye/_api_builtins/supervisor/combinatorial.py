from __future__ import annotations

import random
from typing import TYPE_CHECKING, Dict, Iterable, List

import numpy as np
import z3

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch

# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import SupervisionResult

# noinspection PyProtectedMember
from officialeye._api.template.supervisor import Supervisor

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate

# noinspection PyProtectedMember
from officialeye._internal.context.singleton import get_internal_afi

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye.error.errors.supervision import ErrSupervisionInvalidEngineConfig

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class CombinatorialSupervisor(Supervisor):

    SUPERVISOR_ID = "combinatorial"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(CombinatorialSupervisor.SUPERVISOR_ID, config_dict)

        # setup configuration
        def _min_match_factor_preprocessor(v: str) -> float:

            v = float(v)

            if v > 1.0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.SUPERVISOR_ID}' supervisor",
                    f"The `min_match_factor` value ({v}) cannot exceed 1.0."
                )

            if v < 0.0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.SUPERVISOR_ID}' supervisor",
                    f"The `min_match_factor` value ({v}) cannot be negative."
                )

            return v

        self._min_match_factor = self.config.get("min_match_factor", default=0.1, value_preprocessor=_min_match_factor_preprocessor)

        def _max_transformation_error_preprocessor(v: str) -> int:

            v = int(v)

            if v < 0:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.SUPERVISOR_ID}' supervisor.",
                    f"The `max_transformation_error` value ({v}) cannot be negative."
                )

            if v > 5000:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.SUPERVISOR_ID}' supervisor.",
                    f"The `max_transformation_error` value ({v}) is too high."
                )

            return v

        self._max_transformation_error = self.config.get("max_transformation_error", value_preprocessor=_max_transformation_error_preprocessor)

        def _z3_timeout_preprocessor(v: str) -> int:

            v = int(v)

            if v < 1:
                raise ErrSupervisionInvalidEngineConfig(
                    f"while loading the '{CombinatorialSupervisor.SUPERVISOR_ID}' supervisor.",
                    f"The `z3_timeout` value ({v}) cannot be negative or zero."
                )

            return v

        self._z3_timeout = self.config.get("z3_timeout", default=2500, value_preprocessor=_z3_timeout_preprocessor)

        # initialize all engine-specific values
        self._z3_context: z3.Context | None = None

        # create variables for components of the translation matrix
        self._transformation_matrix: np.ndarray | None = None

        # keys: matches (instances of Match)
        # values: z3 integer variables representing the errors for each match,
        # i.e., how consistent the match is with the affine transformation model
        self._match_weight: Dict[IMatch, z3.ArithRef] = {}

        self._minimum_weight_to_enforce: float | None = None

    def setup(self, template: ITemplate, matching_result: IMatchingResult, /) -> None:

        self._z3_context = z3.Context()

        self._transformation_matrix = np.array([
            [z3.Real("a", ctx=self._z3_context), z3.Real("b", ctx=self._z3_context)],
            [z3.Real("c", ctx=self._z3_context), z3.Real("d", ctx=self._z3_context)]
        ], dtype=z3.AstRef)

        for match in matching_result.get_all_matches():
            self._match_weight[match] = z3.Real(
                f"w_{match.keypoint_point[0]}_{match.keypoint_point[1]}_{match.target_point[0]}_{match.target_point[1]}",
                ctx=self._z3_context
            )

        # calculate the minimum weight that we need to enforce
        self._minimum_weight_to_enforce = matching_result.get_total_match_count() * self._min_match_factor

    def _get_consistency_check(self, match: IMatch, delta: np.ndarray, delta_prime: np.ndarray, /) -> z3.AstRef:
        """
        Generates a z3 formula asserting the consistency of the match with the affine linear transformation model.
        Consistency does not mean ideal matching of coordinates; rather, the template position with the affine
        transformation applied to it, must roughly be equal the target position for consistency to hold.
        """

        assert delta.shape == (2,)
        assert delta_prime.shape == (2,)
        assert match.template_point.shape == (2,)

        translated_template_point = self._transformation_matrix @ (match.template_point - delta) + delta_prime
        translated_template_point_x, translated_template_point_y = translated_template_point

        target_point_x, target_point_y = match.target_point

        return z3.And(
            translated_template_point_x - target_point_x <= self._max_transformation_error,
            target_point_x - translated_template_point_x <= self._max_transformation_error,
            translated_template_point_y - target_point_y <= self._max_transformation_error,
            target_point_y - translated_template_point_y <= self._max_transformation_error,
        )

    def supervise(self, template: ITemplate, matching_result: IMatchingResult, /) -> Iterable[SupervisionResult]:

        weights_lower_bounds = z3.And(*(self._match_weight[match] >= 0 for match in matching_result.get_all_matches()), self._z3_context)
        weights_upper_bounds = z3.And(*(self._match_weight[match] <= 1 for match in matching_result.get_all_matches()), self._z3_context)

        total_weight = z3.Sum(*(self._match_weight[match] for match in matching_result.get_all_matches()))

        solver = z3.Optimize(ctx=self._z3_context)
        solver.set("timeout", self._z3_timeout)

        solver.add(weights_lower_bounds)
        solver.add(weights_upper_bounds)
        solver.add(total_weight >= self._minimum_weight_to_enforce)

        solver.maximize(total_weight)

        for keypoint in template.keypoints:
            keypoint_matches: List[IMatch] = list(matching_result.get_matches_for_keypoint(keypoint.identifier))

            if len(keypoint_matches) == 0:
                continue

            # TODO: think whether this is a good algorithm design decision, and improve it if not
            anchor_match: IMatch = random.choice(keypoint_matches)

            delta = anchor_match.template_point
            delta_prime = anchor_match.target_point

            solver.push()

            for match in matching_result.get_all_matches():
                solver.add(z3.Implies(
                    self._match_weight[match] > 0,
                    # consistency check
                    self._get_consistency_check(match, delta, delta_prime),
                    ctx=self._z3_context
                ))

            result = solver.check()

            if result == z3.unsat:
                get_internal_afi().warn(Verbosity.INFO_VERBOSE, "Could not satisfy the imposed constraints.")
                solver.pop()
                continue

            if result == z3.unknown:
                get_internal_afi().warn(Verbosity.INFO_VERBOSE, "Could not decide the satifiability of the imposed constraints.")
                solver.pop()
                continue

            assert result == z3.sat

            model = solver.model()
            model_evaluator = np.vectorize(lambda var: model.eval(var, model_completion=True).as_fraction())  # noqa: B023

            # extract total weight and maximization target from the model
            model_total_weight = float(model_evaluator(total_weight))

            # extract transformation matrix from model
            transformation_matrix = model_evaluator(self._transformation_matrix)

            """
            delta = np.array([1217, 109], dtype=int)
            delta_prime = np.array([785, 374], dtype=int)
            transformation_matrix = np.array([[0.57689122, 0.01245905], [-0.0564908, 0.59782386]], dtype=float)
            """

            _result = SupervisionResult(
                delta=delta,
                delta_prime=delta_prime,
                transformation_matrix=transformation_matrix,
                score=model_total_weight
            )

            for match in matching_result.get_all_matches():
                match_weight = model_evaluator(self._match_weight[match])
                _result.set_match_weight(match, match_weight)

            yield _result

            solver.pop()
