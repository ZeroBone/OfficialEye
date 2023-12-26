import abc
from abc import ABC
from typing import Union

# noinspection PyPackageRequirements
import cv2

from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template


class IODriver(ABC):

    def __init__(self, driver_id: str):
        self.__driver_id = driver_id

    @abc.abstractmethod
    def output_analyze_result(self, target: cv2.Mat, result: Union[SupervisionResult, None], /):
        raise NotImplementedError()

    @abc.abstractmethod
    def output_show_result(self, template: Template, img: cv2.Mat):
        raise NotImplementedError()
