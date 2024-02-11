from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

import numpy as np

from officialeye._api.config import MutatorConfig

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class IMutator(ABC):

    @property
    def config(self) -> MutatorConfig:
        raise NotImplementedError()

    @abstractmethod
    def mutate(self, img: np.ndarray, /) -> np.ndarray:
        raise NotImplementedError()


class Mutator(IMutator, ABC):

    def __init__(self, mutator_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self.mutator_id = mutator_id

        self._config = MutatorConfig(config_dict, mutator_id)

    @property
    def config(self) -> MutatorConfig:
        return self._config
