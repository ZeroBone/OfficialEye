from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Iterable, List

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.keypoint import IKeypoint

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch, Match

# noinspection PyProtectedMember
from officialeye._api.template.matcher import Matcher
from officialeye.error.errors.matching import ErrMatchingInvalidEngineConfig

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.template import ITemplate
    from officialeye.types import ConfigDict


def _preprocess_sensitivity(value: str, /) -> float:

    value = float(value)

    if value < 0.0:
        raise ErrMatchingInvalidEngineConfig(
            f"while loading the '{SiftFlannMatcher.MATCHER_ID}' keypoint matcher",
            f"The `sensitivity` value ({value}) cannot be negative."
        )

    if value > 1.0:
        raise ErrMatchingInvalidEngineConfig(
            f"while loading the '{SiftFlannMatcher.MATCHER_ID}' keypoint matcher",
            f"The `sensitivity` value ({value}) cannot exceed 1.0."
        )

    return value


class SiftFlannMatcher(Matcher):

    MATCHER_ID = "sift_flann"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(SiftFlannMatcher.MATCHER_ID, config_dict)

        self._sensitivity = self.config.get("sensitivity", default=0.7, value_preprocessor=_preprocess_sensitivity)

        self._img: np.ndarray | None = None
        self._sift = None

        self._keypoints_target = None
        self._destination_target = None
        self._template: ITemplate | None = None
        self._matches: Dict[IKeypoint, List[Match]] | None = {}

    def setup(self, target: np.ndarray, template: ITemplate, /) -> None:

        self._img = cv2.cvtColor(target, cv2.COLOR_BGR2GRAY)

        # initialize the SIFT engine in CV2
        # noinspection PyUnresolvedReferences
        self._sift = cv2.SIFT_create()

        # pre-compute the sift keypoints in the target image
        self._keypoints_target, self._destination_target = self._sift.detectAndCompute(self._img, None)

        self._template = template

        self._matches = {}

    def match(self, keypoint: IKeypoint, /) -> None:

        _original_pattern_image = keypoint.get_image().load()

        pattern = cv2.cvtColor(_original_pattern_image, cv2.COLOR_BGR2GRAY)

        keypoints_pattern, destination_pattern = self._sift.detectAndCompute(pattern, None)

        index_params = {
            "algorithm": 1,
            "trees": 5
        }

        search_params = {
            "checks": 50
        }

        flann = cv2.FlannBasedMatcher(index_params, search_params)
        matches = flann.knnMatch(destination_pattern, self._destination_target, k=2)

        # we need to draw only good matches, so create a mask
        matches_mask = [[0, 0] for _ in range(len(matches))]

        result: List[Match] = []

        # filter matches
        for i, (m, n) in enumerate(matches):

            if m.distance >= self._sensitivity * n.distance:
                continue

            matches_mask[i] = [1, 0]

            pattern_point = keypoints_pattern[m.queryIdx].pt
            target_point = self._keypoints_target[m.trainIdx].pt

            pattern_point_vec = np.array(pattern_point, dtype=int)
            target_point_vec = np.array(target_point, dtype=int)

            match = Match(
                self._template,
                keypoint,
                keypoint_point=pattern_point_vec,
                target_point=target_point_vec
            )

            match.set_score(self._sensitivity * n.distance - m.distance)

            result.append(match)

        # TODO: visualization generation
        """
        # noinspection PyTypeChecker
        debug_image = cv2.drawMatchesKnn(
            pattern,
            keypoints_pattern,
            self._img,
            self._keypoints_target,
            matches,
            None,
            matchColor=(0, 0xff, 0),
            singlePointColor=(0xff, 0, 0),
            matchesMask=matches_mask,
            flags=cv2.DrawMatchesFlags_DEFAULT
        )

        cv2.imwrite(f"test_{keypoint.identifier}.png", debug_image)
        """

        assert keypoint not in self._matches
        self._matches[keypoint] = result

    def get_matches_for_keypoint(self, keypoint: IKeypoint, /) -> Iterable[IMatch]:
        assert keypoint in self._matches
        return self._matches[keypoint]
