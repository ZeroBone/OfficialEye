from typing import Tuple

from officialeye.context.singleton import oe_context


class Match:

    def __init__(self, template_id: str, keypoint_region_id: str,
                 region_point: Tuple[int, int], target_point: Tuple[int, int], /):
        self.template_id = template_id
        self.keypoint_id = keypoint_region_id
        self.region_point = region_point
        self.target_point = target_point

    def get_template_point(self) -> Tuple[int, int]:
        """Returns the region point in the coordinate system of the underlying template."""
        template = oe_context().get_template(self.template_id)
        keypoint = template.get_keypoint(self.keypoint_id)
        # TODO
        return self.region_point

    def __eq__(self, o):
        if not isinstance(o, Match):
            return False
        if self.template_id != o.template_id:
            return False
        if self.keypoint_id != o.keypoint_id:
            return False
        return self.region_point == o.region_point and self.target_point == o.target_point

    def __ne__(self, __value):
        return not self == __value

    def __hash__(self):
        return hash((self.template_id, self.keypoint_id, self.region_point, self.target_point))

    def __str__(self) -> str:
        return "%s_%s: (%4d, %4d) <-> (%4d, %4d)" % (self.template_id, self.keypoint_id,
                                                     self.region_point[0], self.region_point[1],
                                                     self.target_point[0], self.target_point[1])

    def get_debug_identifier(self) -> str:
        return "%s_%s_%04d_%04d_%04d_%04d" % (self.template_id, self.keypoint_id,
                                              self.region_point[0], self.region_point[1],
                                              self.target_point[0], self.target_point[1])
