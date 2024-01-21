from typing import Dict

import cv2

from officialeye._internal.mutation.mutator import Mutator


class GrayscaleMutator(Mutator):

    MUTATOR_ID = "grayscale"

    def __init__(self, config: Dict[str, any], /):
        super().__init__(GrayscaleMutator.MUTATOR_ID, config)

    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:
        return cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
