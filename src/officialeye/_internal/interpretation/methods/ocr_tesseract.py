from typing import Dict

import cv2
import numpy as np
from pytesseract import pytesseract

from officialeye._internal.interpretation.method import InterpretationMethod
from officialeye._internal.interpretation.serializable import Serializable


class TesseractMethod(InterpretationMethod):

    METHOD_ID = "ocr_tesseract"

    def __init__(self, config_dict: Dict[str, any]):
        super().__init__(TesseractMethod.METHOD_ID, config_dict)

        self._tesseract_lang = self.get_config().get("lang", default="eng")
        self._tesseract_config = self.get_config().get("config", default="")

    def interpret(self, feature_img: np.ndarray, template_id: str, feature_id: str, /) -> Serializable:
        return pytesseract.image_to_string(feature_img, lang=self._tesseract_lang, config=self._tesseract_config).strip()
