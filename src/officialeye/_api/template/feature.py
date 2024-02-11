from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Iterable

import numpy as np

from officialeye._api.template.region import IRegion

if TYPE_CHECKING:
    from officialeye._api.mutator import IMutator


class IFeature(IRegion, ABC):

    def __str__(self) -> str:
        return f"Feature '{self.identifier}'"

    @abstractmethod
    def get_mutators(self) -> Iterable[IMutator]:
        """
        Returns:
            A list of mutators from the feature class of the feature, in the order in which they are to be applied.
        """
        raise NotImplementedError()

    def apply_mutators_to_image(self, img: np.ndarray, /) -> np.ndarray:
        """
        Takes an image and applies the mutators defined in the corresponding feature class.

        Arguments:
            img: The image that should be transformed.

        Returns:
            The resulting image.
        """

        for mutator in self.get_mutators():
            img = mutator.mutate(img)

        return img
