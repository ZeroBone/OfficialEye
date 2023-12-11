# noinspection PyPackageRequirements
import cv2

from officialeye.cli_utils import export_and_show_image
from officialeye.keypoint import TemplateKeypoint


def _remove_noise(img):
    # blur
    blur = cv2.GaussianBlur(img, (0, 0), sigmaX=33, sigmaY=33)

    # divide
    divide = cv2.divide(img, blur, scale=255)

    # otsu threshold
    thresh = cv2.threshold(divide, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)[1]

    # apply morphology
    kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (3, 3))
    morph = cv2.morphologyEx(thresh, cv2.MORPH_CLOSE, kernel)

    return morph


FLANN_INDEX_KDTREE = 1


class Matcher:
    def __init__(self, img: cv2.Mat, /, *, debug_mode: bool = False):
        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        self._ratio_thresh = 0.7
        self._debug = debug_mode

    def add_keypoint(self, keypoint: TemplateKeypoint, /):
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
                print(pattern_point, target_point)

        if self._debug:

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

            export_and_show_image(debug_image)

    def match(self):
        pass
