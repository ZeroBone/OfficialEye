import tempfile
from typing import Dict

# noinspection PyPackageRequirements
import cv2
from pytesseract import pytesseract

from officialeye.interpretation import InterpretationMethod, Serializable


class FileTempMethod(InterpretationMethod):

    METHOD_ID = "file_temp"

    def __init__(self, config_dict: Dict[str, any]):
        super().__init__(FileTempMethod.METHOD_ID, config_dict)

        self._format = self.get_config().get("format", default="png")

    def interpret(self, feature_img: cv2.Mat, feature_id: str, /) -> Serializable:

        with tempfile.NamedTemporaryFile(prefix="officialeye_", suffix=f".{self._format}", delete=False) as fp:
            fp.close()

        cv2.imwrite(fp.name, feature_img)

        return fp.name
