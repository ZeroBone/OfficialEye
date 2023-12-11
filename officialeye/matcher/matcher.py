import abc
from abc import ABC
# noinspection PyPackageRequirements
import cv2

from officialeye.debug import DebugInformationContainer
from officialeye.region.keypoint import TemplateKeypoint


class KeypointMatcher(ABC):

    def __init__(self, img: cv2.Mat, /, *, debug: DebugInformationContainer = None):
        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        self._debug = debug

    @abc.abstractmethod
    def match_keypoint(self, keypoint: TemplateKeypoint, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def match_finish(self):
        raise NotImplementedError()

    def in_debug_mode(self, /) -> bool:
        return self._debug is not None

    def debug_export(self):
        self._debug.export()
