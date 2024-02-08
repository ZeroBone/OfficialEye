from __future__ import annotations

from abc import ABC
from typing import Any, TYPE_CHECKING

from officialeye._api.template.region import IRegion, Region


if TYPE_CHECKING:
    from officialeye._api.template.template import ITemplate


class IFeature(IRegion, ABC):

    def __str__(self) -> str:
        return f"Feature '{self.identifier}'"


class Feature(Region, IFeature):

    def __init__(self, template: ITemplate, /, **kwargs):
        super().__init__(template, **kwargs)

    def __eq__(self, o: Any) -> bool:
        return super().__eq__(o)

    def __hash__(self):
        return super().__hash__()
