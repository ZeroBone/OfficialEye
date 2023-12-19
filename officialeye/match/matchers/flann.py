# noinspection PyPackageRequirements
import cv2
import numpy as np

from officialeye.match.match import Match
from officialeye.match.matcher import KeypointMatcher
from officialeye.match.result import KeypointMatchingResult
from officialeye.region.keypoint import TemplateKeypoint

FLANN_INDEX_KDTREE = 1


class FlannKeypointMatcher(KeypointMatcher):

    ENGINE_ID = "flann"

    def __init__(self, template_id: str, img: cv2.Mat, /, **kwargs):
        super().__init__(template_id, img, **kwargs)
        self._ratio_thresh = 0.7  # TODO: make this configurable
        self._debug_images = []
        self._result = KeypointMatchingResult()

    def match_keypoint(self, keypoint: TemplateKeypoint, /):
        # noinspection PyUnresolvedReferences
        sift = cv2.SIFT_create()

        pattern = keypoint.to_image(grayscale=True)
        target = self._img

        keypoints_pattern, destination_pattern = sift.detectAndCompute(pattern, None)
        keypoints_target, destination_target = sift.detectAndCompute(target, None)

        index_params = dict(algorithm=FLANN_INDEX_KDTREE, trees=5)
        search_params = dict(checks=50)  # or pass empty dictionary
        flann = cv2.FlannBasedMatcher(index_params, search_params)
        matches = flann.knnMatch(destination_pattern, destination_target, k=2)

        # we need to draw only good matches, so create a mask
        matches_mask = [[0, 0] for _ in range(len(matches))]

        # filter matches
        for i, (m, n) in enumerate(matches):
            if m.distance < self._ratio_thresh * n.distance:
                matches_mask[i] = [1, 0]

                pattern_point = keypoints_pattern[m.queryIdx].pt
                target_point = keypoints_target[m.trainIdx].pt

                # maybe one should consider rounding values here, instead of simply stripping the floating-point part
                pattern_point = np.array(pattern_point, dtype=int)
                target_point = np.array(target_point, dtype=int)

                match = Match(self.template_id, keypoint.region_id, pattern_point, target_point)
                self._result.add_match(match)

        if self.in_debug_mode():
            # noinspection PyTypeChecker
            debug_image = cv2.drawMatchesKnn(
                pattern,
                keypoints_pattern,
                target,
                keypoints_target,
                matches,
                None,
                matchColor=(0, 0xff, 0),
                singlePointColor=(0xff, 0, 0),
                matchesMask=matches_mask,
                flags=cv2.DrawMatchesFlags_DEFAULT
            )
            self._debug.add_image(debug_image, name=f"match_{keypoint.region_id}")

    def match_finish(self):
        return self._result
