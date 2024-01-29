import abc
from abc import ABC

import cv2

from officialeye.error.error import OEError
from officialeye._internal.supervision.result import SupervisionResult


class IODriver(ABC):

    def __init__(self):
        pass

    @abc.abstractmethod
    def handle_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def handle_error(self, error: OEError, /):
        raise NotImplementedError()
