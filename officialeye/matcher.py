# noinspection PyPackageRequirements
import cv2

from officialeye.cli_utils import export_and_show_image
from officialeye.feature import TemplateFeature


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


def _find_template(img: cv2.Mat, template: cv2.Mat):
    # make the image and template grayscale
    img = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
    template = cv2.cvtColor(template, cv2.COLOR_RGB2GRAY)

    # remove noise from image and template
    img = _remove_noise(img)
    template = _remove_noise(template)

    cv2.imwrite("_d_img.png", img)
    cv2.imwrite("_d_template.png", template)

    # perform actual template matching
    vertices = []

    for method in (cv2.TM_CCOEFF, cv2.TM_CCOEFF_NORMED, cv2.TM_CCORR, cv2.TM_CCORR_NORMED,
                   cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED):
        result = cv2.matchTemplate(img, template, method)
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(result)
        if method in (cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED):
            top_left = min_loc
        else:
            top_left = max_loc
        vertices.append(top_left)

    return vertices


FLANN_INDEX_KDTREE = 1


class Matcher:
    def __init__(self, img: cv2.Mat, /):
        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

    def add_feature(self, feature: TemplateFeature, /):
        # noinspection PyUnresolvedReferences
        sift = cv2.SIFT_create()

        pattern = feature.to_image(grayscale=True)
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
            if m.distance < 0.7 * n.distance:
                matches_mask[i] = [1, 0]
                print(m)

        draw_params = dict(matchColor=(0, 0xff, 0),
                           singlePointColor=(0xff, 0, 0),
                           matchesMask=matches_mask,
                           flags=cv2.DrawMatchesFlags_DEFAULT)

        debug_image = cv2.drawMatchesKnn(
            pattern,
            keypoints_pattern,
            target,
            keypoints_target,
            matches,
            None,
            **draw_params
        )

        export_and_show_image(debug_image)

        """
        vertices = _find_template()
        feature.find_on_image(target)

        source_points.append([x, y])
        source_points.append([x + f.w, y])
        source_points.append([x + f.w, y + f.h])
        source_points.append([x, y + f.h])

        destination_points.append([f.x, f.y])
        destination_points.append([f.x + f.w, f.y])
        destination_points.append([f.x + f.w, f.y + f.h])
        destination_points.append([f.x, f.y + f.h])

        # img = cv2.rectangle(img, (x, y), (x + f.w, y + f.h), (0, 0, 0xff), 4)
        for (x, y), color in zip(vertices, [(0, 0, 0xff), (0, 0xff, 0), (0xff, 0, 0), (0, 0xff, 0xff), (0xff, 0xff, 0),
                                            (0xff, 0, 0xff), (0xff, 0xff, 0xff)]):
            img = cv2.rectangle(img, (x, y), (x + f.w, y + f.h), color, 4)
        """

    def match(self):
        pass
