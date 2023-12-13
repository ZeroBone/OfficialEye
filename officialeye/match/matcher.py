import abc
from abc import ABC

# noinspection PyPackageRequirements
import cv2

from officialeye.debug.container import DebugContainer
from officialeye.debug.debuggable import Debuggable
from officialeye.match.result import KeypointMatchingResult
from officialeye.region.keypoint import TemplateKeypoint


class KeypointMatcher(ABC, Debuggable):

    def __init__(self, template_id: str, img: cv2.Mat, /, *, debug: DebugContainer = None):
        super().__init__(debug=debug)
        self.template_id = template_id
        self._img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

    @abc.abstractmethod
    def match_keypoint(self, keypoint: TemplateKeypoint, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def match_finish(self) -> KeypointMatchingResult:
        raise NotImplementedError()
