from typing import List

import cv2

from officialeye._api.mutator import Mutator
from officialeye._api.context import Context


class Image:

    def __init__(self, context: Context, /, *, path: str):
        self._context = context
        self._mutators: List[Mutator] = []
        self._path = path

    def load(self) -> cv2.Mat:

        img = cv2.imread(self._path, cv2.IMREAD_COLOR)

        for mutator in self._mutators:
            img = mutator.mutate(img)

        return img

    def apply_mutators(self, *mutators: Mutator):
        self._mutators += mutators
