from __future__ import annotations

from typing import TYPE_CHECKING

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator
from officialeye.error.errors.template import ErrTemplateInvalidMutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class RotateMutator(Mutator):
    """
    Mutator that rotates the image clockwise by the specified angle.
    """

    MUTATOR_ID = "rotate"

    def __init__(self, config: ConfigDict, /):
        super().__init__(RotateMutator.MUTATOR_ID, config)

        def _angle_preprocessor(angle_text: str) -> int:
            angle = int(angle_text)

            if angle not in (0, 90, 180, 270):
                raise ErrTemplateInvalidMutator(
                    f"while loading mutator '{self.mutator_id}'.",
                    f"The 'angle' parameter must be a multiple of 90 degrees, got {angle}."
                )

            return angle

        self._angle = self.config.get("angle", value_preprocessor=_angle_preprocessor)

    def mutate(self, img: np.ndarray, /) -> np.ndarray:

        if self._angle == 0:
            # we do not need to rotate the image at all
            return img

        if self._angle == 90:
            cv2_rotate_code = cv2.ROTATE_90_CLOCKWISE
        elif self._angle == 180:
            cv2_rotate_code = cv2.ROTATE_180
        elif self._angle == 270:
            cv2_rotate_code = cv2.ROTATE_90_COUNTERCLOCKWISE
        else:
            raise AssertionError()

        return cv2.rotate(img, cv2_rotate_code)
