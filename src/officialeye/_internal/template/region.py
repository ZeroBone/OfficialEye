from __future__ import annotations

from typing import Dict, TYPE_CHECKING

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.region import IRegion
from officialeye._internal.context.singleton import get_internal_context


if TYPE_CHECKING:
    from officialeye._internal.template.template import InternalTemplate


class InternalRegion(IRegion):

    def __init__(self, template_id: str, region_dict: Dict[str, any], /):
        self._template_id = template_id
        self._region_id = str(region_dict["id"])
        self._x = int(region_dict["x"])
        self._y = int(region_dict["y"])
        self._w = int(region_dict["w"])
        self._h = int(region_dict["h"])

    @property
    def identifier(self) -> str:
        return self._region_id

    @property
    def x(self) -> int:
        return self._x

    @property
    def y(self) -> int:
        return self._y

    @property
    def w(self) -> int:
        return self._w

    @property
    def h(self) -> int:
        return self._h

    @property
    def template(self) -> InternalTemplate:
        return get_internal_context().get_template(self._template_id)

    def insert_into_image(self, target: np.ndarray, transformed_version: np.ndarray = None):

        assert target.shape[0] == self.template.height
        assert target.shape[1] == self.template.width

        if transformed_version is None:
            transformed_version = self.get_image().load()

        target[self.y: self.y + self.h, self.x: self.x + self.w] = transformed_version
