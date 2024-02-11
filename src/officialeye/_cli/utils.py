from typing import Tuple

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature

# noinspection PyProtectedMember
from officialeye._api.template.keypoint import IKeypoint

# noinspection PyProtectedMember
from officialeye._api.template.region import IRegion

_LABEL_COLOR_DEFAULT = (0, 0, 0xff)
_VISUALIZATION_SCALE_COEFF = 1.0 / 1400.0

_FEATURE_RECT_COLOR = (0, 0xff, 0)
_KEYPOINT_RECT_COLOR = (0, 0, 0xff)


def visualize_region(region: IRegion, img: np.ndarray, /, *, rect_color: Tuple[int, int, int], label_color=_LABEL_COLOR_DEFAULT) -> np.ndarray:

    img = cv2.rectangle(img, (region.x, region.y), (region.x + region.w, region.y + region.h), rect_color, 4)

    label_origin = (
        region.x + int(10 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
        region.y + int(30 * img.shape[0] * _VISUALIZATION_SCALE_COEFF)
    )

    font_scale = img.shape[0] * _VISUALIZATION_SCALE_COEFF
    img = cv2.putText(
        img,
        region.identifier,
        label_origin,
        cv2.FONT_HERSHEY_SIMPLEX,
        font_scale,
        label_color,
        int(2 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
        cv2.LINE_AA
    )

    return img


def visualize_feature(feature: IFeature, img: np.ndarray, /) -> np.ndarray:
    return visualize_region(feature, img, rect_color=_FEATURE_RECT_COLOR)


def visualize_keypoint(keypoint: IKeypoint, img: np.ndarray, /) -> np.ndarray:
    return visualize_region(keypoint, img, rect_color=_KEYPOINT_RECT_COLOR)
