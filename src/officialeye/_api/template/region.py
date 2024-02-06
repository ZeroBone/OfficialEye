from __future__ import annotations

from typing import TYPE_CHECKING, Any

import numpy as np

# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.crop import CropMutator

if TYPE_CHECKING:
    from officialeye._api.image import Image
    from officialeye._api.template.template import Template


class Region:

    def __init__(self, template: Template, /, *, identifier: str, x: int, y: int, w: int, h: int):
        self._template = template
        self._identifier = identifier
        self._x = x
        self._y = y
        self._w = w
        self._h = h

    def __eq__(self, o: Any) -> bool:

        if not isinstance(o, Region):
            return False

        return self._template.identifier == o._template.identifier and self.identifier == o.identifier

    def __hash__(self):
        return hash((self._template.identifier, self._identifier))

    @property
    def identifier(self) -> str:
        return self._identifier

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

    def get_image(self) -> Image:
        _mutator = CropMutator(dict(x=self.x, y=self.y, w=self.w, h=self.h))
        _img: Image = self._template.get_mutated_image()
        _img.apply_mutators(_mutator)
        return _img

    @property
    def top_left(self) -> np.ndarray:
        return np.array([self.x, self.y])

    @property
    def top_right(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y])

    @property
    def bottom_left(self) -> np.ndarray:
        return np.array([self.x, self.y + self.h])

    @property
    def bottom_right(self) -> np.ndarray:
        return np.array([self.x + self.w, self.y + self.h])


class Feature(Region):

    def __init__(self, template: Template, /, **kwargs):
        super().__init__(template, **kwargs)

    def __eq__(self, o: Any) -> bool:
        return super().__eq__(o)

    def __hash__(self):
        return super().__hash__()


class Keypoint(Region):

    def __init__(self, template: Template, /, *, matches_min: int, matches_max: int, **kwargs):
        super().__init__(template, **kwargs)

        self._matches_min = matches_min
        self._matches_max = matches_max

    def __eq__(self, o: Any) -> bool:
        return super().__eq__(o)

    def __hash__(self):
        return super().__hash__()

    @property
    def matches_min(self) -> int:
        return self._matches_min

    @property
    def matches_max(self) -> int:
        return self._matches_max
