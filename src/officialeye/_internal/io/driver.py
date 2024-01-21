import abc
from abc import ABC

import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.error import OEError
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.template.template import Template


class IODriver(ABC):

    def __init__(self, context: Context):
        self._context = context

    @abc.abstractmethod
    def handle_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def handle_show_result(self, template: Template, img: cv2.Mat, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def handle_error(self, error: OEError, /):
        raise NotImplementedError()
