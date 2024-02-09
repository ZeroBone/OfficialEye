import abc
from typing import Dict

import numpy as np

from officialeye._internal.interpretation.config import InterpretationMethodConfig
from officialeye._internal.interpretation.serializable import Serializable


# TODO: abstract out interpretation methods into the API


class InterpretationMethod(abc.ABC):

    def __init__(self, method_id: str, config_dict: Dict[str, any], /):
        super().__init__()

        self.method_id = method_id

        self._config = InterpretationMethodConfig(config_dict, method_id)

    def get_config(self) -> InterpretationMethodConfig:
        return self._config

    @abc.abstractmethod
    def interpret(self, feature_img: np.ndarray, template_id: str, feature_id: str, /) -> Serializable:
        raise NotImplementedError()
