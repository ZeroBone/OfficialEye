import abc
from abc import ABC

# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.debug.debuggable import Debuggable
from officialeye.match.result import KeypointMatchingResult
from officialeye.region.keypoint import TemplateKeypoint


class KeypointMatcher(ABC, Debuggable):

    def __init__(self, engine_id: str, template_id: str, img: cv2.Mat, /):
        super().__init__()

        self.__engine_id = engine_id
        self.__default_config = None

        self.template_id = template_id
        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

    @abc.abstractmethod
    def match_keypoint(self, keypoint: TemplateKeypoint, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def match_finish(self) -> KeypointMatchingResult:
        raise NotImplementedError()

    def _set_default_config(self, default_config: dict):
        self.__default_config = default_config

    def get_template(self):
        return oe_context().get_template(self.template_id)

    def get_config(self) -> dict:

        assert self.__default_config is not None, "get_config() should not be called if there is no default configuration configured"

        matching_config = self.get_template().get_supervision_config()

        if self.__engine_id in matching_config:
            return matching_config[self.__engine_id]

        return self.__default_config
