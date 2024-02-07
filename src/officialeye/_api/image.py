import os
from abc import ABC, abstractmethod
from typing import List

import cv2
import numpy as np

from officialeye._api.mutator import IMutator
from officialeye._api.context import Context
from officialeye.error.errors.io import ErrIOInvalidPath


class IImage(ABC):

    def __init__(self):
        super().__init__()

    @abstractmethod
    def load(self) -> np.ndarray:
        raise NotImplementedError()

    @abstractmethod
    def apply_mutators(self, *mutators: IMutator):
        raise NotImplementedError()


class Image(IImage):

    def __init__(self, context: Context, /, *, path: str):
        super().__init__()

        self._context = context
        self._mutators: List[IMutator] = []
        self._path = path

    def load(self) -> np.ndarray:

        if not os.path.isfile(self._path):
            raise ErrIOInvalidPath(
                f"while loading image located at '{self._path}'.",
                f"This path does not refer to a file."
            )

        if not os.access(self._path, os.R_OK):
            raise ErrIOInvalidPath(
                f"while loading image located at '{self._path}'.",
                f"The file at this path is not readable."
            )

        img = cv2.imread(self._path, cv2.IMREAD_COLOR)

        for mutator in self._mutators:
            img = mutator.mutate(img)

        return img

    def apply_mutators(self, *mutators: IMutator):
        self._mutators += mutators
