from __future__ import annotations

import abc
from typing import TYPE_CHECKING

import cv2

from officialeye._api.config import MutatorConfig


if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class Mutator(abc.ABC):

    def __init__(self, mutator_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self.mutator_id = mutator_id

        self._config = MutatorConfig(config_dict, mutator_id)

    @property
    def config(self) -> MutatorConfig:
        return self._config

    @abc.abstractmethod
    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:
        raise NotImplementedError()
