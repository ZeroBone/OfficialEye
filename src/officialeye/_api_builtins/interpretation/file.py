from __future__ import annotations

import os
from typing import TYPE_CHECKING

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.interpretation import Interpretation

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.feature import IFeature
    from officialeye.types import ConfigDict, FeatureInterpretation


class FileInterpretation(Interpretation):

    INTERPRETATION_ID = "file"

    def __init__(self, config_dict: ConfigDict, /):
        super().__init__(FileInterpretation.INTERPRETATION_ID, config_dict)

        self._path = self.config.get("path", value_preprocessor=str)

    def interpret(self, feature_img: np.ndarray, feature: IFeature, /) -> FeatureInterpretation:

        os.makedirs(os.path.dirname(self._path), exist_ok=True)

        cv2.imwrite(self._path, feature_img)

        return None
