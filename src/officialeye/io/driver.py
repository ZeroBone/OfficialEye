import abc
from abc import ABC

# noinspection PyPackageRequirements
import cv2

from officialeye.error import OEError
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template


class IODriver(ABC):

    def __init__(self):
        pass

    @abc.abstractmethod
    def output_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def output_show_result(self, template: Template, img: cv2.Mat, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def output_error(self, error: OEError, /):
        raise NotImplementedError()
