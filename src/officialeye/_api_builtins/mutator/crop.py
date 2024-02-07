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

        self.config.set_value_preprocessor("x", int)
        self.config.set_value_preprocessor("y", int)
        self.config.set_value_preprocessor("w", int)
        self.config.set_value_preprocessor("h", int)

        self._x = self.config.get("x", default=0)
        self._y = self.config.get("y", default=0)
        self._w = self.config.get("w")
        self._h = self.config.get("h")

    def mutate(self, img: np.ndarray, /) -> np.ndarray:
        return img[self._y:self._y + self._h, self._x:self._x + self._w]
