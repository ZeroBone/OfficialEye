from abc import ABC

from officialeye._api.template.region import IRegion


class IFeature(IRegion, ABC):

    def __str__(self) -> str:
        return f"Feature '{self.identifier}'"
