from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

import numpy as np

from officialeye._api.config import InterpretationConfig
from officialeye._api.template.feature import IFeature

if TYPE_CHECKING:
    from officialeye.types import ConfigDict, FeatureInterpretation


class IInterpretation(ABC):

    @property
    def config(self) -> InterpretationConfig:
        raise NotImplementedError()

    @abstractmethod
    def interpret(self, feature_img: np.ndarray, feature: IFeature, /) -> FeatureInterpretation:
        raise NotImplementedError()


class Interpretation(IInterpretation, ABC):

    def __init__(self, interpretation_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self.interpretation_id = interpretation_id

        self._config = InterpretationConfig(config_dict, interpretation_id)

    @property
    def config(self) -> InterpretationConfig:
        return self._config
