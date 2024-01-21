import abc
from typing import Dict

import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.interpretation.serializable import Serializable
from officialeye._internal.interpretation.config import InterpretationMethodConfig


class InterpretationMethod(abc.ABC):

    def __init__(self, context: Context, method_id: str, config_dict: Dict[str, any], /):
        super().__init__()

        self._context = context
        self.method_id = method_id

        self._config = InterpretationMethodConfig(config_dict, method_id)

    def get_config(self) -> InterpretationMethodConfig:
        return self._config

    @abc.abstractmethod
    def interpret(self, feature_img: cv2.Mat, template_id: str, feature_id: str, /) -> Serializable:
        raise NotImplementedError()
