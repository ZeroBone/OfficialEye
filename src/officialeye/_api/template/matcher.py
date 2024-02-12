from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Iterable

import numpy as np

from officialeye._api.config import MatcherConfig
from officialeye._api.template.keypoint import IKeypoint
from officialeye._api.template.match import IMatch

if TYPE_CHECKING:
    from officialeye._api.template.template import ITemplate
    from officialeye.types import ConfigDict


class IMatcher(ABC):

    @property
    @abstractmethod
    def config(self) -> MatcherConfig:
        raise NotImplementedError()

    @abstractmethod
    def setup(self, target: np.ndarray, template: ITemplate, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def match(self, keypoint: IKeypoint, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def get_matches_for_keypoint(self, keypoint: IKeypoint, /) -> Iterable[IMatch]:
        raise NotImplementedError()


class Matcher(IMatcher, ABC):

    def __init__(self, matcher_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self.matcher_id = matcher_id

        self._config = MatcherConfig(config_dict, matcher_id)

    @property
    def config(self) -> MatcherConfig:
        return self._config
