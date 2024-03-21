from __future__ import annotations

from typing import TYPE_CHECKING, Iterable, List, Dict

import numpy as np
import random
import pyscipopt as scip
from scipy.stats.distributions import chi2

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

from abc import ABC, abstractmethod


class Model(ABC):
    @abstractmethod
    def fit(self, pts):
        ...

    @abstractmethod
    def error(self, data):
        ...

    @abstractmethod
    def predict(self, data):
        ...

    @staticmethod
    @abstractmethod
    def get_complexity():
        ...


def ransac(data, model_type, tolerance, prob_inlier, p=0.99):
    """
    Random sample consensus (RANSAC)
    :param data: Data to fit
    :param model_type: Model subclass
    :param tolerance: Tolerance on the error to consider a point inlier to a model
    :param prob_inlier: Probability that a point is an inlier (inliers / (inliers + outliers))
    :param p: Desired probability that there is at least one good sample
    :return: A model of type model_type, fitted to the inliers
    """

    m = model_type.get_complexity()
    best_num_inliers = 0
    n = data.shape[0]
    max_times = int(np.ceil(np.log(1 - p) / np.log(1 - prob_inlier ** m)))
    satisfactory_inlier_ratio = prob_inlier * n

    inliers = []
    for _ in range(max_times):
        pts = data[random.sample(range(n), m)]
        model = model_type()
        model.fit(pts)
        error = model.error(data)
        num_inliers = (error < tolerance).sum()
        if num_inliers / n > satisfactory_inlier_ratio:
            inliers = data[error < tolerance]
            break
        if num_inliers > best_num_inliers:
            best_num_inliers = num_inliers
            inliers = data[error < tolerance]

    model = model_type()
    model.fit(inliers)

    return model


def prosac(data, quality, model_type, tolerance, beta, eta0, psi,
           max_outlier_proportion, p_good_sample, max_number_of_draws,
           enable_n_star_optimization=True):
    """
    Progressive random sampling algorithm (PROSAC)
    Adapted from: http://devernay.free.fr/vision/src/prosac.c
    :param data: Data to fit
    :param quality: Point quality
    :param model_type: Model subclass
    :param tolerance: Tolerance on the error to consider a point inlier to a model
    :param beta: Probability that a match is declared inlier by mistake, i.e. the ratio of the "inlier"
    :param eta0: Maximum probability that a solution with more than In_star inliers in Un_star exists and was not found after k samples (typically set to 5%, see Sec. 2.2 of [Chum-Matas-05]).
    :param psi: Probability that In_star out of n_star data points are by chance inliers to an arbitrary (typically set to 5%)
    :param max_outlier_proportion: Maximum allowed outliers proportion in the input data, used to compute T_N (can be as high as 0.95)
    :param p_good_sample: Probability that at least one of the random samples picked up by RANSAC is free of outliers
    :param max_number_of_draws: Max number of draws
    :param enable_n_star_optimization: Enable early stopping if the probability of finding a better match fall below eta0
    :return: A model of type model_type, fitted to the inliers
    """

    indexes = np.argsort(quality)
    data = data[indexes[::-1]]

    num_points = data.shape[0]
    num_points_to_sample = model_type.get_complexity()
    chi2_value = chi2.isf(2 * psi, 1)

    def niter_ransac(p, epsilon, s, n_max):
        """
        Compute the maximum number of iterations for RANSAC
        :param p: Probability that at least one of the random samples picked up by RANSAC is free of outliers
        :param epsilon: Proportion of outliers
        :param s: Sample size
        :param n_max: Upper bound on the number of iterations (-1 means INT_MAX)
        :return: maximum number of iterations for RANSAC
        """
        if n_max == -1:
            n_max = np.iinfo(np.int32).max
        if not (n_max >= 1):
            raise ValueError('n_max must be positive')
        if epsilon <= 0:
            return 1
        logarg = - np.exp(s * np.log(1 - epsilon))
        logval = np.log(1 + logarg)
        n = np.log(1 - p) / logval
        if logval < 0 and n < n_max:
            return np.ceil(n)
        return n_max

    def i_min(m, n, beta):
        """
        Non-randomness, prevent from choosing a model supported by outliers
        :param m: Model complexity
        :param n: Number of considered points
        :param beta: Beta parameter
        :return: Minimum number of inlier to avoid model only supported by outliers
        """
        mu = n * beta
        sigma = np.sqrt(n * beta * (1 - beta))
        return np.ceil(m + mu + sigma * np.sqrt(chi2_value))

    N = num_points
    m = num_points_to_sample
    T_N = niter_ransac(p_good_sample, max_outlier_proportion, num_points_to_sample, -1)
    I_N_min = (1 - max_outlier_proportion) * N

    n_star = N
    I_n_star = 0
    I_N_best = 0
    t = 0
    n = m
    T_n = T_N

    for i in range(m):
        T_n = T_n * (n - i) / (N - i)

    T_n_prime = 1
    k_n_star = T_N

    while ((I_N_best < I_N_min) or t <= k_n_star) and t < T_N and t <= max_number_of_draws:
        t = t + 1

        if (t > T_n_prime) and (n < n_star):
            T_nplus1 = (T_n * (n + 1)) / (n + 1 - m)
            n = n + 1
            T_n_prime = T_n_prime + np.ceil(T_nplus1 - T_n)
            T_n = T_nplus1

        if t > T_n_prime:
            pts_idx = np.random.choice(n, m, replace=False)
        else:
            pts_idx = np.append(np.random.choice(n - 1, m - 1, replace=False), n)

        sample = data[pts_idx]

        # 3. Model parameter estimation
        model = model_type()
        model.fit(sample)

        # 4. Model verification
        error = model.error(data)
        is_inlier = (error < tolerance)
        I_N = is_inlier.sum()

        if I_N > I_N_best:
            I_N_best = I_N
            n_best = N
            I_n_best = I_N
            best_model = model

            if enable_n_star_optimization:
                epsilon_n_best = I_n_best / n_best
                I_n_test = I_N
                for n_test in range(N, m, -1):
                    if not (n_test >= I_n_test):
                        raise RuntimeError('Loop invariant broken: n_test >= I_n_test')
                    if ((I_n_test * n_best > I_n_best * n_test) and (I_n_test > epsilon_n_best * n_test + np.sqrt(
                            n_test * epsilon_n_best * (1 - epsilon_n_best) * chi2_value))):
                        if I_n_test < i_min(m, n_test, beta):
                            break
                        n_best = n_test
                        I_n_best = I_n_test
                        epsilon_n_best = I_n_best / n_best
                    I_n_test = I_n_test - is_inlier[n_test - 1]

            if I_n_best * n_star > I_n_star * n_best:
                if not (n_best >= I_n_best):
                    raise RuntimeError('Assertion not respected: n_best >= I_n_best')
                n_star = n_best
                I_n_star = I_n_best
                k_n_star = niter_ransac(1 - eta0, 1 - I_n_star / n_star, m, T_N)

    return best_model


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

    def get_squared_error(self, match: IMatch, /) -> float:

        predicted_terget_point = self.predict(match.template_point)
        actual_target_point = match.target_point

        error = actual_target_point - predicted_terget_point

        return np.dot(error, error)

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
                match for match in matching_result.get_all_matches() if maybe_good_model.get_squared_error(match) < self._t
            ]

            get_internal_afi().info(Verbosity.DEBUG_VERBOSE, f"Good matches count: {len(good_matches)} Threshold: {self._d}")

            if len(good_matches) > self._d:
                better_model = AffineTransformationModel()
                better_model.fit(good_matches)

                better_model_mse = 0.0
                for match in good_matches:
                    better_model_mse += better_model.get_squared_error(match) * match.get_score()

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
        n = 5
        # a threshold value to determine data points that are fit well by the model (inlier)
        t = 225
        # the number of close data points (inliers) required to assert that the model fits well to the data
        d = 10  # int(0.1 * total_match_count)

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
