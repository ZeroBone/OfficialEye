# noinspection PyPackageRequirements
import cv2

from officialeye.region import TemplateRegion


_FEATURE_RECT_COLOR = (0, 0xff, 0)


class TemplateFeature(TemplateRegion):
    def __init__(self, feature_dict: dict, template, /):
        super().__init__(feature_dict, template)

    def draw(self, img: cv2.Mat, /):
        return super()._draw(img, rect_color=_FEATURE_RECT_COLOR)
