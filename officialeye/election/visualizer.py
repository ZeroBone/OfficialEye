# noinspection PyPackageRequirements
import cv2

from officialeye.election.result import ElectionResult


class ElectionResultVisualizer:

    def __init__(self, result: ElectionResult):
        self._result = result

    def render(self) -> cv2.Mat:
        pass
