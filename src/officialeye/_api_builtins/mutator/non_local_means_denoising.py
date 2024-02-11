from __future__ import annotations

from typing import TYPE_CHECKING

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator
from officialeye.error.errors.template import ErrTemplateInvalidMutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class NonLocalMeansDenoisingMutator(Mutator):

    MUTATOR_ID = "non_local_means_denoising"

    def __init__(self, config: ConfigDict, /):
        super().__init__(NonLocalMeansDenoisingMutator.MUTATOR_ID, config)

        # load data from configuration
        self._colored_mode = self.config.get("colored", default=True, value_preprocessor=bool)

        self._conf_h = self.config.get("h", default=10, value_preprocessor=int)
        self._conf_hForColorComponents = self.config.get("hForColorComponents", default=10, value_preprocessor=int)
        self._conf_templateWindowSize = self.config.get("templateWindowSize", default=7, value_preprocessor=int)
        self._conf_searchWindowSize = self.config.get("searchWindowSize", default=21, value_preprocessor=int)

        # validate templateWindowSize
        if self._conf_templateWindowSize < 1:
            raise ErrTemplateInvalidMutator(
                f"while loading mutator '{self.mutator_id}'.",
                f"The 'templateWindowSize' parameter must be positive, got '{self._conf_templateWindowSize}'."
            )

        if self._conf_templateWindowSize % 2 == 0:
            raise ErrTemplateInvalidMutator(
                f"while loading mutator '{self.mutator_id}'.",
                f"The 'templateWindowSize' parameter must be odd, got '{self._conf_templateWindowSize}'."
            )

        # validate searchWindowSize
        if self._conf_searchWindowSize < 1:
            raise ErrTemplateInvalidMutator(
                f"while loading mutator '{self.mutator_id}'.",
                f"The 'searchWindowSize' parameter must be positive, got '{self._conf_searchWindowSize}'."
            )

        if self._conf_searchWindowSize % 2 == 0:
            raise ErrTemplateInvalidMutator(
                f"while loading mutator '{self.mutator_id}'.",
                f"The 'searchWindowSize' parameter must be odd, got '{self._conf_searchWindowSize}'."
            )

    def mutate(self, img: np.ndarray, /) -> np.ndarray:

        if self._colored_mode:
            return cv2.fastNlMeansDenoisingColored(
                img,
                None,
                self._conf_h,
                self._conf_hForColorComponents,
                self._conf_templateWindowSize,
                self._conf_searchWindowSize
            )

        return cv2.fastNlMeansDenoising(
            img,
            None,
            self._conf_h,
            self._conf_templateWindowSize,
            self._conf_searchWindowSize
        )
