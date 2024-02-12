from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Any

import numpy as np

from officialeye._api.template.keypoint import IKeypoint

if TYPE_CHECKING:
    from officialeye._api.template.template import ITemplate


class IMatch(ABC):

    @property
    @abstractmethod
    def template(self) -> ITemplate:
        raise NotImplementedError()

    @property
    @abstractmethod
    def keypoint(self) -> IKeypoint:
        raise NotImplementedError()

    @property
    @abstractmethod
    def keypoint_point(self) -> np.ndarray:
        raise NotImplementedError()

    @property
    @abstractmethod
    def target_point(self) -> np.ndarray:
        raise NotImplementedError()

    @abstractmethod
    def get_score(self) -> float:
        raise NotImplementedError()

    @property
    def template_point(self) -> np.ndarray:
        """Returns the coordinates of the point lying in the keypoint, in the coordinate system of the underlying template."""
        return self.keypoint_point + self.keypoint.top_left

    def __str__(self) -> str:
        return (f"Point ({self.target_point[0]}, {self.target_point[1]}) matches ({self.keypoint_point[0]}, {self.keypoint_point[1]}) "
                f"in '{self.keypoint}' of '{self.template.identifier}'.")

    def __eq__(self, o: Any) -> bool:

        if not isinstance(o, IMatch):
            return False

        if self.template != o.template:
            return False

        if self.keypoint != o.keypoint:
            return False

        return (np.array_equal(self.keypoint_point, o.keypoint_point)
                and np.array_equal(self.target_point, o.target_point))

    def __lt__(self, o: Any) -> bool:
        assert isinstance(o, Match)
        return self.get_score() < o.get_score()

    def __hash__(self):
        return hash((
            self.template.identifier,
            self.keypoint.identifier,
            np.dot(self.keypoint_point, self.keypoint_point),
            np.dot(self.target_point, self.target_point)
        ))


class Match(IMatch):

    # TODO: remove the first argument from the constructor, and possibly create InternalMatch and ExternalMatch instances
    def __init__(self, template: ITemplate, keypoint: IKeypoint, /, *,
                 keypoint_point: np.ndarray, target_point: np.ndarray, score: float = 0.0):
        super().__init__()

        self._template = template
        self._keypoint = keypoint

        self._keypoint_point = keypoint_point
        self._target_point = target_point

        self._score = score

    def get_score(self) -> float:
        return self._score

    def set_score(self, new_score: float, /):
        self._score = new_score

    @property
    def template(self) -> ITemplate:
        return self._template

    @property
    def keypoint(self) -> IKeypoint:
        return self._keypoint

    @property
    def keypoint_point(self) -> np.ndarray:
        return self._keypoint_point.copy()

    @property
    def target_point(self) -> np.ndarray:
        return self._target_point.copy()
