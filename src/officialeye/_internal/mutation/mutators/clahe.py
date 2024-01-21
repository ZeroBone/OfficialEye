from typing import Dict

import cv2

from officialeye._internal.mutation.mutator import Mutator


class CLAHEMutator(Mutator):
    """
    Implementation of constrast increase via Contrast Limited Adaptive Histogram Equalization.
    """

    MUTATOR_ID = "clahe"

    def __init__(self, config: Dict[str, any], /):
        super().__init__(CLAHEMutator.MUTATOR_ID, config)

    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:

        lab = cv2.cvtColor(img, cv2.COLOR_BGR2LAB)
        l_channel, a, b = cv2.split(lab)

        # apply CLAHE to the L-channel
        # TODO: make parameters configurable
        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))

        cl = clahe.apply(l_channel)

        # merge the CLAHE enhanced L-channel with the a and b channels
        limg = cv2.merge((cl, a, b))

        # convert back to BGR color space
        return cv2.cvtColor(limg, cv2.COLOR_LAB2BGR)
