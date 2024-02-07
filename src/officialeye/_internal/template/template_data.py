from typing import List

# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator


class TemplateDataRegion:

    def __init__(self, /, *, identifier: str, x: int, y: int, w: int, h: int):
        self.identifier = identifier
        self.x = x
        self.y = y
        self.w = w
        self.h = h

    def get_init_args(self) -> dict:
        return dict(
            identifier=self.identifier,
            x=self.x,
            y=self.y,
            w=self.w,
            h=self.h
        )


class TemplateDataFeature(TemplateDataRegion):

    def __init__(self, /, **kwargs):
        super().__init__(**kwargs)


class TemplateDataKeypoint(TemplateDataRegion):

    def __init__(self, /, *, matches_min: int, matches_max: int, **kwargs):
        super().__init__(**kwargs)

        self.matches_min = matches_min
        self.matches_max = matches_max

    def get_init_args(self) -> dict:
        return {
            **super().get_init_args(),
            "matches_min": self.matches_min,
            "matches_max": self.matches_max
        }


class TemplateData:

    def __init__(self, /, *, identifier: str, name: str, source: str, width: int, height: int,
                 features: List[TemplateDataFeature], keypoints: List[TemplateDataKeypoint],
                 source_mutators: List[IMutator], target_mutators: List[IMutator]):

        self.identifier = identifier
        self.name = name
        self.source = source

        self.width = width
        self.height = height

        self.features = features
        self.keypoints = keypoints

        self.source_mutators = source_mutators
        self.target_mutators = target_mutators
