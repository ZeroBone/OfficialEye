import abc
from abc import ABC

import numpy as np

from officialeye.error.error import OEError
from officialeye._internal.supervision.result import SupervisionResult


# TODO: get rid of this module completely


class IODriver(ABC):

    def __init__(self):
        pass

    @abc.abstractmethod
    def handle_supervision_result(self, target: np.ndarray, result: SupervisionResult, /):
        raise NotImplementedError()

    @abc.abstractmethod
    def handle_error(self, error: OEError, /):
        raise NotImplementedError()
