from typing import Dict

# noinspection PyPackageRequirements
import cv2
from pytesseract import pytesseract

from officialeye.interpretation import InterpretationMethod


class TesseractInterpretationMethod(InterpretationMethod):

    METHOD_ID = "ocr_tesseract"

    def __init__(self, config_dict: Dict[str, any]):
        super().__init__(TesseractInterpretationMethod.METHOD_ID, config_dict)

        self._tesseract_lang = self.get_config().get("lang", default="eng")
        self._tesseract_config = self.get_config().get("config", default="--dpi 10000 --oem 3 --psm 6")

    def interpret(self, feature_img: cv2.Mat, feature_id: str, /) -> any:
        return pytesseract.image_to_string(feature_img, lang=self._tesseract_lang, config=self._tesseract_config).strip()
