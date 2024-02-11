from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

from officialeye._api.template.feature import IFeature

if TYPE_CHECKING:
    from officialeye._api.template.template_interface import ITemplate
    from officialeye.types import FeatureInterpretation


class IInterpretationResult(ABC):

    @property
    @abstractmethod
    def template(self) -> ITemplate:
        raise NotImplementedError()

    @abstractmethod
    def get_feature_interpretation(self, feature: IFeature, /) -> FeatureInterpretation:
        raise NotImplementedError()
