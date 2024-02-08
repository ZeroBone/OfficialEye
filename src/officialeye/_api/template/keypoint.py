from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, TYPE_CHECKING

from officialeye._api.template.region import IRegion, Region


if TYPE_CHECKING:
    from officialeye._api.template.template import ITemplate


class IKeypoint(IRegion, ABC):

    @property
    @abstractmethod
    def matches_min(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def matches_max(self) -> int:
        raise NotImplementedError()

    def __str__(self) -> str:
        return f"Keypoint '{self.identifier}'"


class Keypoint(Region, IKeypoint):

    def __init__(self, template: ITemplate, /, *, matches_min: int, matches_max: int, **kwargs):
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
