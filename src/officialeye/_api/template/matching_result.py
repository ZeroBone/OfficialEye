from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Iterable

from officialeye._api.template.match import IMatch

if TYPE_CHECKING:
    from officialeye._api.template.template_interface import ITemplate


class IMatchingResult(ABC):

    @property
    @abstractmethod
    def template(self) -> ITemplate:
        raise NotImplementedError()

    @abstractmethod
    def get_all_matches(self) -> Iterable[IMatch]:
        raise NotImplementedError()

    @abstractmethod
    def get_total_match_count(self) -> int:
        raise NotImplementedError()

    @abstractmethod
    def get_matches_for_keypoint(self, keypoint_id: str, /) -> Iterable[IMatch]:
        raise NotImplementedError()
