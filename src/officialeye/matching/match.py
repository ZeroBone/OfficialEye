import numpy as np

from officialeye.context.singleton import oe_context
from officialeye.template.region.keypoint import TemplateKeypoint


class Match:

    def __init__(self, template_id: str, keypoint_region_id: str,
                 region_point: np.ndarray, target_point: np.ndarray, /, *, score: float = 0.0):
        assert region_point.shape[0] == 2
        assert target_point.shape[0] == 2
        self.template_id = template_id
        self.keypoint_id = keypoint_region_id
        self._region_point = region_point
        self._target_point = target_point
        self._score = score

    def set_score(self, new_score: float, /):
        self._score = new_score

    def get_score(self) -> float:
        return self._score

    def get_template_point(self) -> np.ndarray:
        return self._region_point.copy()

    def get_original_template_point(self) -> np.ndarray:
        """Returns the region point in the coordinate system of the underlying template."""
        template = oe_context().get_template(self.template_id)
        keypoint = template.get_keypoint(self.keypoint_id)
        return self._region_point + keypoint.get_top_left_vec()

    def get_keypoint(self) -> TemplateKeypoint:
        return oe_context().get_template(self.template_id).get_keypoint(self.keypoint_id)

    def get_target_point(self) -> np.ndarray:
        return self._target_point.copy()

    def __lt__(self, other) -> bool:
        assert isinstance(other, Match)
        return self.get_score() < other.get_score()

    def __eq__(self, o):
        if not isinstance(o, Match):
            return False
        if self.template_id != o.template_id:
            return False
        if self.keypoint_id != o.keypoint_id:
            return False
        return (np.array_equal(self._region_point, o._region_point)
                and np.array_equal(self._target_point, o._target_point))

    def __ne__(self, __value):
        return not self == __value

    def __hash__(self):
        return hash((self.template_id, self.keypoint_id, np.dot(self._region_point, self._target_point)))

    def __str__(self) -> str:
        return "%s_%s: (%4d, %4d) <-> (%4d, %4d)" % (self.template_id, self.keypoint_id,
                                                     int(self._region_point[0]), int(self._region_point[1]),
                                                     int(self._target_point[0]), int(self._target_point[1]))

    def get_debug_identifier(self) -> str:
        return "%s_%s_%04d_%04d_%04d_%04d" % (self.template_id, self.keypoint_id,
                                              int(self._region_point[0]), int(self._region_point[1]),
                                              int(self._target_point[0]), int(self._target_point[1]))
