from typing import Dict

import cv2

from officialeye._internal.error.errors.template import ErrTemplateInvalidMutator
from officialeye._internal.mutation.mutator import Mutator


class NonLocalMeansDenoisingMutator(Mutator):

    MUTATOR_ID = "non_local_means_denoising"

    def __init__(self, config: Dict[str, any], /):
        super().__init__(NonLocalMeansDenoisingMutator.MUTATOR_ID, config)

        # setup configuration loading

        self.get_config().set_value_preprocessor("colored", bool)
        self.get_config().set_value_preprocessor("h", int)
        self.get_config().set_value_preprocessor("hForColorComponents", int)
        self.get_config().set_value_preprocessor("templateWindowSize", int)
        self.get_config().set_value_preprocessor("searchWindowSize", int)

        # load data from configuration

        self._colored_mode = self.get_config().get("colored", default=True)

        self._conf_h = self.get_config().get("h", default=10)
        self._conf_hForColorComponents = self.get_config().get("hForColorComponents", default=10)
        self._conf_templateWindowSize = self.get_config().get("templateWindowSize", default=7)
        self._conf_searchWindowSize = self.get_config().get("searchWindowSize", default=21)

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

    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:

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
