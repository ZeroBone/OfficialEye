from typing import Dict

# noinspection PyPackageRequirements
import cv2

from officialeye.region.region import TemplateRegion

_FEATURE_RECT_COLOR = (0, 0xff, 0)


class TemplateFeatureMeta:

    def __init__(self, meta_dict: Dict[str, any], /):
        self._meta_dict = meta_dict

    def get(self, key: str, /, *, default_value=None):
        if key in self._meta_dict:
            return self._meta_dict[key]
        return default_value


class TemplateFeature(TemplateRegion):
    def __init__(self, feature_dict: dict, template, /):
        super().__init__(feature_dict, template)

        _meta_dict = feature_dict["meta"] if "meta" in feature_dict else {}

        self._meta = TemplateFeatureMeta(_meta_dict)

    def get_meta(self) -> TemplateFeatureMeta:
        return self._meta

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_FEATURE_RECT_COLOR)
