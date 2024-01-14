# noinspection PyPackageRequirements
import cv2
import numpy as np

from officialeye.error.errors.matching import ErrMatchingInvalidEngineConfig
from officialeye.matching.match import Match
from officialeye.matching.matcher import KeypointMatcher
from officialeye.matching.result import KeypointMatchingResult

_FLANN_INDEX_KDTREE = 1


class SiftFlannKeypointMatcher(KeypointMatcher):

    ENGINE_ID = "sift_flann"

    def __init__(self, template_id: str, img: cv2.Mat, /):
        super().__init__(SiftFlannKeypointMatcher.ENGINE_ID, template_id, img)

        def _preprocess_sensitivity(value: any) -> float:

            value = float(value)

            if value < 0.0:
                raise ErrMatchingInvalidEngineConfig(
                    f"while loading the '{SiftFlannKeypointMatcher.ENGINE_ID}' keypoint matcher",
                    f"The `sensitivity` value ({self._sensitivity}) cannot be negative."
                )

            if value > 1.0:
                raise ErrMatchingInvalidEngineConfig(
                    f"while loading the '{SiftFlannKeypointMatcher.ENGINE_ID}' keypoint matcher",
                    f"The `sensitivity` value ({self._sensitivity}) cannot exceed 1.0."
                )

            return value

        self.get_config().set_value_preprocessor("sensitivity", _preprocess_sensitivity)

        self._sensitivity = self.get_config().get("sensitivity", default=0.7)

        self._debug_images = []
        self._result = KeypointMatchingResult(template_id)

        # initialize the SIFT engine in CV2
        # noinspection PyUnresolvedReferences
        self._sift = cv2.SIFT_create()

        # pre-compute the sift keypoints in the target image
        self._keypoints_target, self._destination_target = self._sift.detectAndCompute(self._img, None)

    def match_keypoint(self, pattern: cv2.Mat, keypoint_id: str, /):

        pattern = cv2.cvtColor(pattern, cv2.COLOR_BGR2GRAY)

        keypoints_pattern, destination_pattern = self._sift.detectAndCompute(pattern, None)

        index_params = {
            "algorithm": _FLANN_INDEX_KDTREE,
            "trees": 5
        }

        search_params = {
            "checks": 50
        }

        flann = cv2.FlannBasedMatcher(index_params, search_params)
        matches = flann.knnMatch(destination_pattern, self._destination_target, k=2)

        # we need to draw only good matches, so create a mask
        matches_mask = [[0, 0] for _ in range(len(matches))]

        # filter matches
        for i, (m, n) in enumerate(matches):
            if m.distance < self._sensitivity * n.distance:
                matches_mask[i] = [1, 0]

                pattern_point = keypoints_pattern[m.queryIdx].pt
                target_point = self._keypoints_target[m.trainIdx].pt

                # maybe one should consider rounding values here, instead of simply stripping the floating-point part
                pattern_point = np.array(pattern_point, dtype=int)
                target_point = np.array(target_point, dtype=int)

                match = Match(self.template_id, keypoint_id, pattern_point, target_point)
                match.set_score(self._sensitivity * n.distance - m.distance)
                self._result.add_match(match)

        if self.in_debug_mode():
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
            self._debug.add_image(debug_image, name=f"match_{keypoint_id}")

    def match_finish(self):
        return self._result
