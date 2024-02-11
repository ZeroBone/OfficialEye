from __future__ import annotations

from typing import TYPE_CHECKING

import numpy as np
from pytesseract import pytesseract

# noinspection PyProtectedMember
from officialeye._api.template.interpretation import Interpretation

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.feature import IFeature
    from officialeye.types import ConfigDict, FeatureInterpretation


class TesseractInterpretation(Interpretation):

    INTERPRETATION_ID = "ocr_tesseract"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(TesseractInterpretation.INTERPRETATION_ID, config_dict)

        self._tesseract_lang = self.config.get("lang", default="eng", value_preprocessor=str)
        self._tesseract_config = self.config.get("config", default="", value_preprocessor=str)

    def interpret(self, feature_img: np.ndarray, feature: IFeature, /) -> FeatureInterpretation:
        return pytesseract.image_to_string(feature_img, lang=self._tesseract_lang, config=self._tesseract_config).strip()
