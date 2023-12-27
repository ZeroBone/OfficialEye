# noinspection PyPackageRequirements
import cv2

from officialeye.region.region import TemplateRegion

_FEATURE_RECT_COLOR = (0, 0xff, 0)


class TemplateFeature(TemplateRegion):
    def __init__(self, feature_dict: dict, template, /):
        super().__init__(feature_dict, template)

        assert "type" in feature_dict
        self._type = feature_dict["type"]

    def get_type(self) -> str:
        return self._type

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_FEATURE_RECT_COLOR)
