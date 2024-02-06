from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Iterable

import numpy as np

from officialeye._api.template.region import Keypoint
from officialeye._api.config import MatcherConfig


if TYPE_CHECKING:
    from officialeye._api.template.template import Template
    from officialeye.types import ConfigDict


class Match:

    def __init__(self, template: Template, keypoint: Keypoint, /, *,
                 region_point: np.ndarray, target_point: np.ndarray, score: float = 0.0):
        self._template = template
        self._keypoint = keypoint

        self._region_point = region_point
        self._target_point = target_point

        self._score = score

    def get_score(self):
        return self._score

    def set_score(self, new_score: float, /):
        self._score = new_score

    def get_template(self) -> Template:
        return self._template

    def get_keypoint(self) -> Keypoint:
        return self._keypoint

    def get_template_point(self) -> np.ndarray:
        return self._region_point.copy()

    def get_original_template_point(self) -> np.ndarray:
        """Returns the coordinates of the point lying in the keypoint, in the coordinate system of the underlying template."""
        return self._region_point + self.get_keypoint().top_left

    def get_target_point(self) -> np.ndarray:
        return self._target_point.copy()


class Matcher(ABC):

    def __init__(self, matcher_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self.matcher_id = matcher_id

        self._config = MatcherConfig(config_dict, matcher_id)

    @property
    def config(self) -> MatcherConfig:
        return self._config

    @abstractmethod
    def setup(self, template: Template, /):
        raise NotImplementedError()

    @abstractmethod
    def match(self, keypoint: Keypoint, /):
        raise NotImplementedError()

    @abstractmethod
    def get_matches_for_keypoint(self, keypoint: Keypoint, /) -> Iterable[Match]:
        raise NotImplementedError()
