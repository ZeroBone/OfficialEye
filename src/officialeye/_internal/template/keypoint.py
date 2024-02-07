from officialeye._api.template.keypoint import IKeypoint
from officialeye.error.errors.template import ErrTemplateInvalidKeypoint
from officialeye._internal.template.region import InternalRegion


class InternalKeypoint(InternalRegion, IKeypoint):

    def __init__(self, template_id: str, keypoint_dict: dict, /):
        super().__init__(template_id, keypoint_dict)

        self._matches_min = keypoint_dict["matches"]["min"]
        self._matches_max = keypoint_dict["matches"]["max"]

        if self._matches_max < self._matches_min:
            raise ErrTemplateInvalidKeypoint(
                f"while loading template keypoint '{self.identifier}'",
                f"the lower bound on the match count ({self._matches_min}) exceeds the upper bound ({self._matches_max})"
            )

        if self._matches_min < 0:
            raise ErrTemplateInvalidKeypoint(
                f"while loading template keypoint '{self.identifier}'",
                f"the lower bound on the match count ({self._matches_min}) cannot be negative"
            )

        assert 0 <= self._matches_min <= self._matches_max

    @property
    def matches_min(self) -> int:
        return self._matches_min

    @property
    def matches_max(self) -> int:
        return self._matches_max
