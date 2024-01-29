from abc import ABC
from typing import Dict

import numpy as np

from officialeye._internal.context.singleton import get_internal_context


class TemplateRegion(ABC):

    def __init__(self, template_id: str, region_dict: Dict[str, any], /):
        self._template_id = template_id

        self.region_id = str(region_dict["id"])
        self.x = int(region_dict["x"])
        self.y = int(region_dict["y"])
        self.w = int(region_dict["w"])
        self.h = int(region_dict["h"])

    def get_template(self):
        return get_internal_context().get_template(self._template_id)

    def get_top_left_vec(self) -> np.ndarray:
        return np.array([self.x, self.y])

    def get_top_right_vec(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y])

    def get_bottom_left_vec(self) -> np.ndarray:
        return np.array([self.x, self.y + self.h])

    def get_bottom_right_vec(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y + self.h])

    def to_image(self):
        img = self.get_template().load_source_image()
        return img[self.y:self.y + self.h, self.x:self.x + self.w]

    def insert_into_image(self, target: np.ndarray, transformed_version: np.ndarray = None):

        assert target.shape[0] == self.get_template().height
        assert target.shape[1] == self.get_template().width

        if transformed_version is None:
            transformed_version = self.to_image()

        target[self.y: self.y + self.h, self.x: self.x + self.w] = transformed_version
