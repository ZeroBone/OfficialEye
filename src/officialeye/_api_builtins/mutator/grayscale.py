from __future__ import annotations

from typing import TYPE_CHECKING

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class GrayscaleMutator(Mutator):

    MUTATOR_ID = "grayscale"

    def __init__(self, config: ConfigDict, /):
        super().__init__(GrayscaleMutator.MUTATOR_ID, config)

    def mutate(self, img: np.ndarray, /) -> np.ndarray:
        return cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
