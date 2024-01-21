from typing import Dict

import cv2

from officialeye._internal.error.errors.template import ErrTemplateInvalidMutator
from officialeye._internal.mutation.mutator import Mutator


class RotateMutator(Mutator):
    """
    Mutator that rotates the image clockwise by the specified angle.
    """

    MUTATOR_ID = "rotate"

    def __init__(self, config: Dict[str, any], /):
        super().__init__(RotateMutator.MUTATOR_ID, config)

        def _angle_preprocessor(angle_text: str) -> int:
            angle = int(angle_text)

            if angle not in (0, 90, 180, 270):
                raise ErrTemplateInvalidMutator(
                    f"while loading mutator '{self.mutator_id}'.",
                    f"The 'angle' parameter must be a multiple of 90 degrees, got {angle}."
                )

            return angle

        self.get_config().set_value_preprocessor("angle", _angle_preprocessor)

        self._angle = self.get_config().get("angle")

    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:

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
            assert False

        return cv2.rotate(img, cv2_rotate_code)
