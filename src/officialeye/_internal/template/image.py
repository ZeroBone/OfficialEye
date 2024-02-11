import os
from typing import List

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.image import IImage

# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator
from officialeye._internal.context.singleton import get_internal_afi
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye.error.errors.io import ErrIOInvalidPath


class InternalImage(IImage):

    def __init__(self, /, *, path: str):
        super().__init__()

        self._mutators: List[IMutator] = []
        self._path = path

    def load(self) -> np.ndarray:

        if not os.path.isfile(self._path):
            raise ErrIOInvalidPath(
                f"while loading image located at '{self._path}'.",
                "This path does not refer to a file."
            )

        if not os.access(self._path, os.R_OK):
            raise ErrIOInvalidPath(
                f"while loading image located at '{self._path}'.",
                "The file at this path is not readable."
            )

        img = cv2.imread(self._path, cv2.IMREAD_COLOR)

        for mutator in self._mutators:
            get_internal_afi().info(Verbosity.DEBUG, f"InternalImage::load() applies mutator '{mutator}'")
            img = mutator.mutate(img)

        return img

    def apply_mutators(self, *mutators: IMutator):
        self._mutators += mutators
