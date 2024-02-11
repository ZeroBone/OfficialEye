from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Any

import numpy as np

# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.crop import CropMutator

if TYPE_CHECKING:
    from officialeye._api.image import IImage
    from officialeye._api.template.template import ITemplate


class IRegion(ABC):

    @property
    @abstractmethod
    def identifier(self) -> str:
        raise NotImplementedError()

    @property
    @abstractmethod
    def x(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def y(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def w(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def h(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def template(self) -> ITemplate:
        raise NotImplementedError()

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

    def get_image(self) -> IImage:
        _mutator = CropMutator(dict(x=self.x, y=self.y, w=self.w, h=self.h))
        _img: IImage = self.template.get_mutated_image()
        _img.apply_mutators(_mutator)
        return _img

    def insert_into_image(self, target: np.ndarray, transformed_version: np.ndarray = None):

        assert target.shape[0] == self.template.height
        assert target.shape[1] == self.template.width

        if transformed_version is None:
            transformed_version = self.get_image().load()

        target[self.y: self.y + self.h, self.x: self.x + self.w] = transformed_version

    def __str__(self) -> str:
        return f"Region '{self.identifier}'"

    def __eq__(self, o: Any) -> bool:

        if not isinstance(o, Region):
            return False

        return self.template.identifier == o.template.identifier and self.identifier == o.identifier

    def __hash__(self):
        return hash((self.template, self.identifier))


class Region(IRegion):

    def __init__(self, template: ITemplate, /, *, identifier: str, x: int, y: int, w: int, h: int):
        self._template = template
        self._identifier = identifier
        self._x = x
        self._y = y
        self._w = w
        self._h = h

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

    @property
    def template(self) -> ITemplate:
        return self._template
