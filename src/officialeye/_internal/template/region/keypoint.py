import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.template import ErrTemplateInvalidKeypoint
from officialeye._internal.template.region.region import TemplateRegion

_KEYPOINT_RECT_COLOR = (0, 0, 0xff)


class TemplateKeypoint(TemplateRegion):
    def __init__(self, context: Context, template_id: str, keypoint_dict: dict, /):
        super().__init__(context, template_id, keypoint_dict)

        self._matches_min = keypoint_dict["matches"]["min"]
        self._matches_max = keypoint_dict["matches"]["max"]

        if self._matches_max < self._matches_min:
            raise ErrTemplateInvalidKeypoint(
                f"while loading template keypoint '{self.region_id}'",
                f"the lower bound on the match count ({self._matches_min}) exceeds the upper bound ({self._matches_max})"
            )

        if self._matches_min < 0:
            raise ErrTemplateInvalidKeypoint(
                f"while loading template keypoint '{self.region_id}'",
                f"the lower bound on the match count ({self._matches_min}) cannot be negative"
            )

        assert 0 <= self._matches_min <= self._matches_max

    def get_matches_min(self) -> int:
        return self._matches_min

    def get_matches_max(self) -> int:
        return self._matches_max

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_KEYPOINT_RECT_COLOR)
