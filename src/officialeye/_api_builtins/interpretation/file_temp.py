from __future__ import annotations

import tempfile
from typing import TYPE_CHECKING

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.interpretation import Interpretation

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.feature import IFeature
    from officialeye.types import ConfigDict, FeatureInterpretation


class FileTempInterpretation(Interpretation):

    INTERPRETATION_ID = "file_temp"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(FileTempInterpretation.INTERPRETATION_ID, config_dict)

        self._format = self.config.get("format", default="png", value_preprocessor=str)

    def interpret(self, feature_img: np.ndarray, feature: IFeature, /) -> FeatureInterpretation:

        with tempfile.NamedTemporaryFile(prefix="officialeye_", suffix=f".{self._format}", delete=False) as fp:
            fp.close()

        cv2.imwrite(fp.name, feature_img)

        return fp.name
