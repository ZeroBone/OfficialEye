from __future__ import annotations

from typing import TYPE_CHECKING, Iterable, List, Dict

import numpy as np
import pyscipopt as scip

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

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class AffineTransformationModelFitter:

    def __init__(self, matches: Iterable[IMatch], /):
        self._model = scip.Model()

        _transformation_matrix_var_x1 = self._model.addVar("mat_x1", vtype="C")
        _transformation_matrix_var_x2 = self._model.addVar("mat_x2", vtype="C")
        _transformation_matrix_var_y1 = self._model.addVar("mat_y1", vtype="C")
        _transformation_matrix_var_y2 = self._model.addVar("mat_y2", vtype="C")

        self._transformation_matrix = np.array([
            [_transformation_matrix_var_x1, _transformation_matrix_var_x2],
            [_transformation_matrix_var_y1, _transformation_matrix_var_y2]
        ])

        _offset_var_x = self._model.addVar("off_x", vtype="C")
        _offset_var_y = self._model.addVar("off_y", vtype="C")

        self._offset = np.array([_offset_var_x, _offset_var_y])

        self._max_transformation_error = self._model.addVar("mte", vtype="C")

        for match in matches:
            self._add_consistency_check(match)

        self._model.setObjective(self._max_transformation_error, "minimize")

    def _add_consistency_check(self, match: IMatch, /) -> None:

        assert match.template_point.shape == (2,)

        translated_template_point = self._transformation_matrix @ match.template_point + self._offset
        translated_template_point_x, translated_template_point_y = translated_template_point

        target_point_x, target_point_y = match.target_point

        self._model.addCons(translated_template_point_x - target_point_x <= self._max_transformation_error)
        self._model.addCons(target_point_x - translated_template_point_x <= self._max_transformation_error)
        self._model.addCons(translated_template_point_y - target_point_y <= self._max_transformation_error)
        self._model.addCons(target_point_y - translated_template_point_y <= self._max_transformation_error)

    def fit(self) -> AffineTransformationRepr:
        self._model.hideOutput()
        self._model.optimize()

        unwrap = np.vectorize(lambda var: self._model.getVal(var))

        return AffineTransformationRepr(
            unwrap(self._transformation_matrix),
            unwrap(self._offset)
        )


class AffineTransformationRepr:

    def __init__(self, matrix: np.ndarray, offset: np.ndarray, /):
        self._matrix: np.ndarray = matrix
        self._offset: np.ndarray = offset

    @property
    def matrix(self) -> np.ndarray:
        return self._matrix

    @property
    def offset(self) -> np.ndarray:
        return self._offset


class AffineTransformationModel:

    def __init__(self):
        self._repr: AffineTransformationRepr | None = None

    def fit(self, matches: Iterable[IMatch], /) -> None:
        fitter = AffineTransformationModelFitter(matches)
        self._repr = fitter.fit()

    def predict(self, template_point: np.ndarray, /) -> np.ndarray:
        return self._repr.matrix @ template_point + self._repr.offset

    def get_prediction_error(self, match: IMatch, /) -> float:

        predicted_terget_point = self.predict(match.template_point)
        actual_target_point = match.target_point

        error = actual_target_point - predicted_terget_point

        return np.sqrt(np.dot(error, error))

    def get_repr(self) -> AffineTransformationRepr:
        return self._repr


class RansacModel:

    def __init__(self, /, *, k: int = 100, n: int, t: float, d: int):
        self._k = k
        self._n = n
        self._t = t
        self._d = d

        self._best_model: AffineTransformationModel | None = None

    def _get_random_match_sample(self, template: ITemplate, matching_result: IMatchingResult, /) -> Iterable[IMatch]:

        matches_pool: List[IMatch] = list(matching_result.get_all_matches())

        relevant_keypoint_ids = set(match.keypoint.identifier for match in matches_pool)
        relevant_keypoint_count = len(relevant_keypoint_ids)

        assert relevant_keypoint_count >= 1
        assert relevant_keypoint_count <= len(list(template.keypoints))

        matches_for_relevant_keypoints: Dict[str, int] = {}

        for keypoint_id in relevant_keypoint_ids:
            matches_for_relevant_keypoints[keypoint_id] = len(list(matching_result.get_matches_for_keypoint(keypoint_id)))

        pool_probability_distribution = [
            1.0 / (relevant_keypoint_count * matches_for_relevant_keypoints[match.keypoint.identifier])
            for match in matches_pool
        ]

        # TODO: imprecise comparison
        assert np.sum(pool_probability_distribution) == 1.0

        rng = np.random.default_rng()

        # noinspection PyTypeChecker
        return rng.choice(matches_pool, self._n, replace=False, p=pool_probability_distribution)

    def fit(self, template: ITemplate, matching_result: IMatchingResult, /) -> None:

        self._best_model = None
        best_model_mse: float = np.inf

        for iter_num in range(1, self._k + 1):

            get_internal_afi().info(Verbosity.DEBUG_VERBOSE, f"Starting ransac iteration {iter_num}.")

            maybe_good_matches = self._get_random_match_sample(template, matching_result)
            maybe_good_model = AffineTransformationModel()
            maybe_good_model.fit(maybe_good_matches)

            # matches that have low error with respect to the maybe_good_model created above
            good_matches: List[IMatch] = [
                match for match in matching_result.get_all_matches() if maybe_good_model.get_prediction_error(match) < self._t
            ]

            get_internal_afi().info(Verbosity.DEBUG_VERBOSE, f"Good matches count: {len(good_matches)} Threshold: {self._d}")

            if len(good_matches) > self._d:
                better_model = AffineTransformationModel()
                better_model.fit(good_matches)

                better_model_mse = 0.0
                for match in good_matches:
                    predicted_terget_point = better_model.predict(match.template_point)
                    actual_target_point = match.target_point
                    error_vec = predicted_terget_point - actual_target_point
                    better_model_mse += np.dot(error_vec, error_vec)

                better_model_mse /= len(good_matches)

                if better_model_mse < best_model_mse:
                    self._best_model = better_model
                    best_model_mse = better_model_mse

    def get_result(self) -> AffineTransformationRepr | None:

        if self._best_model is None:
            return None

        return self._best_model.get_repr()


class RansacSupervisor(Supervisor):

    SUPERVISOR_ID = "ransac"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(RansacSupervisor.SUPERVISOR_ID, config_dict)

    def setup(self, template: ITemplate, matching_result: IMatchingResult, /) -> None:
        pass

    def supervise(self, template: ITemplate, matching_result: IMatchingResult, /) -> Iterable[SupervisionResult]:

        total_match_count = matching_result.get_total_match_count()

        # the minimum number of data points required to estimate the model parameters
        n = 15
        # a threshold value to determine data points that are fit well by the model (inlier)
        t = 10
        # the number of close data points (inliers) required to assert that the model fits well to the data
        d = int(0.1 * total_match_count)

        get_internal_afi().info(Verbosity.DEBUG, f"Ransac params: n={n} t={t} d={d} Total match count: {total_match_count}")

        model = RansacModel(n=n, t=t, d=d)
        model.fit(template, matching_result)
        result = model.get_result()

        if result is None:
            return []

        return [
            SupervisionResult(
                delta=np.array([0.0, 0.0]),
                delta_prime=result.offset,
                transformation_matrix=result.matrix
            )
        ]
