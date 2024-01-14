import abc
from abc import ABC

# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.debug.debuggable import Debuggable
from officialeye.matching.matcher_config import KeypointMatcherConfig
from officialeye.matching.result import KeypointMatchingResult
from officialeye.util.logger import oe_warn


class KeypointMatcher(ABC, Debuggable):

    def __init__(self, engine_id: str, template_id: str, img: cv2.Mat, /):
        super().__init__()

        self.__engine_id = engine_id
        self.template_id = template_id

        # retreive configurations for all keypoint matching engines
        matching_config = self.get_template().get_matching_config()

        assert isinstance(matching_config, dict)

        # get the configuration for the particular engine of interest
        if self.__engine_id in matching_config:
            config_dict = matching_config[self.__engine_id]
        else:
            oe_warn(f"Could not find any configuration entries for the '{self.__engine_id}' matching engine that is being used.")
            config_dict = {}

        self._config = KeypointMatcherConfig(config_dict, engine_id)

        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

    @abc.abstractmethod
    def match_keypoint(self, pattern: cv2.Mat, keypoint_id: str, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def match_finish(self) -> KeypointMatchingResult:
        raise NotImplementedError()

    def get_template(self):
        return oe_context().get_template(self.template_id)

    def get_config(self) -> KeypointMatcherConfig:
        return self._config
