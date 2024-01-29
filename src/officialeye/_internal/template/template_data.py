from typing import List

import cv2

# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator
# noinspection PyProtectedMember
from officialeye._api.template.region import Feature, Keypoint


class TemplateData:

    def __init__(self, /, *, identifier: str, name: str, source: str, width: int, height: int,
                 features: List[Feature], keypoints: List[Keypoint],
                 source_mutators: List[Mutator], target_mutators: List[Mutator]):

        self.identifier = identifier
        self.name = name
        self.source = source

        self.width = width
        self.height = height

        self.features = features
        self.keypoints = keypoints

        self.source_mutators = source_mutators
        self.target_mutators = target_mutators

    def apply_source_mutators(self, img: cv2.Mat, /) -> cv2.Mat:
        for mutator in self.source_mutators:
            img = mutator.mutate(img)
        return img

    def apply_target_mutators(self, img: cv2.Mat, /) -> cv2.Mat:
        for mutator in self.target_mutators:
            img = mutator.mutate(img)
        return img
