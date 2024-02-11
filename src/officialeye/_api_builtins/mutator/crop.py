from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class CropMutator(Mutator):

    MUTATOR_ID = "crop"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(CropMutator.MUTATOR_ID, config_dict)

        self._x = self.config.get("x", default=0, value_preprocessor=int)
        self._y = self.config.get("y", default=0, value_preprocessor=int)
        self._w = self.config.get("w", value_preprocessor=int)
        self._h = self.config.get("h", value_preprocessor=int)

    def mutate(self, img: np.ndarray, /) -> np.ndarray:
        return img[self._y:self._y + self._h, self._x:self._x + self._w]
