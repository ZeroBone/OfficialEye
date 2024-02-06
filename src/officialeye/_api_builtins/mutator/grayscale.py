from __future__ import annotations

from typing import TYPE_CHECKING

import cv2

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator


if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class GrayscaleMutator(Mutator):

    MUTATOR_ID = "grayscale"

    def __init__(self, config: ConfigDict, /):
        super().__init__(GrayscaleMutator.MUTATOR_ID, config)

    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:
        return cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
