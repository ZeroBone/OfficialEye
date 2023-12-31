from typing import Dict

# noinspection PyPackageRequirements
import cv2

from officialeye.error.errors.template import ErrTemplateInvalidFeature
from officialeye.region.region import TemplateRegion

_FEATURE_RECT_COLOR = (0, 0xff, 0)


class TemplateFeatureMeta:

    def __init__(self, meta_dict: Dict[str, any], /):
        self._meta_dict = meta_dict

    def get(self, key: str, expected_type, /, *, default=None):

        assert default is None or isinstance(default, expected_type)

        if key not in self._meta_dict:
            return default

        _value = self._meta_dict[key]

        if not isinstance(_value, expected_type):
            raise ErrTemplateInvalidFeature(
                f"while retreiving meta value by key '{key}'.",
                "The value is of incorrect type."
            )

        return _value


class TemplateFeature(TemplateRegion):
    def __init__(self, feature_dict: dict, template, /):
        super().__init__(feature_dict, template)

        _meta_dict = feature_dict["meta"] if "meta" in feature_dict else {}

        self._meta = TemplateFeatureMeta(_meta_dict)

    def get_meta(self) -> TemplateFeatureMeta:
        return self._meta

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_FEATURE_RECT_COLOR)
