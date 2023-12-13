# noinspection PyPackageRequirements
import cv2

from officialeye.region.region import TemplateRegion

_KEYPOINT_RECT_COLOR = (0, 0, 0xff)


class TemplateKeypoint(TemplateRegion):
    def __init__(self, feature_dict: dict, template, /):
        super().__init__(feature_dict, template)

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_KEYPOINT_RECT_COLOR)
