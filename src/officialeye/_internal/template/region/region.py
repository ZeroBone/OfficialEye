import abc
from typing import Tuple, Dict

import cv2
import numpy as np

from officialeye._internal.context.context import Context

_LABEL_COLOR_DEFAULT = (0, 0, 0xff)
_VISUALIZATION_SCALE_COEFF = 1.0 / 1400.0


class TemplateRegion(abc.ABC):

    def __init__(self, context: Context, template_id: str, region_dict: Dict[str, any], /):
        self._context = context
        self._template_id = template_id

        self.region_id = str(region_dict["id"])
        self.x = int(region_dict["x"])
        self.y = int(region_dict["y"])
        self.w = int(region_dict["w"])
        self.h = int(region_dict["h"])

    def get_template(self):
        return self._context.get_template(self._template_id)

    @abc.abstractmethod
    def visualize(self, img: cv2.Mat) -> cv2.Mat:
        raise NotImplementedError()

    def get_top_left_vec(self) -> np.ndarray:
        return np.array([self.x, self.y])

    def get_top_right_vec(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y])

    def get_bottom_left_vec(self) -> np.ndarray:
        return np.array([self.x, self.y + self.h])

    def get_bottom_right_vec(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y + self.h])

    def _visualize(self, img: cv2.Mat, /, *,
                   rect_color: Tuple[int, int, int], label_color=_LABEL_COLOR_DEFAULT) -> cv2.Mat:
        img = cv2.rectangle(img, (self.x, self.y), (self.x + self.w, self.y + self.h), rect_color, 4)
        label_origin = (
            self.x + int(10 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
            self.y + int(30 * img.shape[0] * _VISUALIZATION_SCALE_COEFF)
        )
        font_scale = img.shape[0] * _VISUALIZATION_SCALE_COEFF
        img = cv2.putText(
            img,
            self.region_id,
            label_origin,
            cv2.FONT_HERSHEY_SIMPLEX,
            font_scale,
            label_color,
            int(2 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
            cv2.LINE_AA
        )
        return img

    def to_image(self):
        img = self.get_template().load_source_image()
        return img[self.y:self.y + self.h, self.x:self.x + self.w]

    def insert_into_image(self, target: np.ndarray, transformed_version: np.ndarray = None):

        assert target.shape[0] == self.get_template().height
        assert target.shape[1] == self.get_template().width

        if transformed_version is None:
            transformed_version = self.to_image()

        target[self.y: self.y + self.h, self.x: self.x + self.w] = transformed_version
