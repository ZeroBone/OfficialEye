from __future__ import annotations

from typing import TYPE_CHECKING, Dict

from officialeye import Context

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature

# noinspection PyProtectedMember
from officialeye._api.template.interpretation_result import IInterpretationResult

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate
from officialeye._internal.api_implementation import IApiInterfaceImplementation
from officialeye._internal.template.external_template import ExternalTemplate

if TYPE_CHECKING:
    from officialeye._internal.template.internal_template import InternalTemplate
    from officialeye.types import FeatureInterpretation


class ExternalInterpretationResult(IInterpretationResult, IApiInterfaceImplementation):

    def __init__(self, template: InternalTemplate, feature_interpretations: Dict[str, FeatureInterpretation], /):
        self._template = ExternalTemplate(template)
        self._feature_interpretation = feature_interpretations

    @property
    def template(self) -> ITemplate:
        return self._template

    def get_feature_interpretation(self, feature: IFeature, /) -> FeatureInterpretation:

        if feature.identifier in self._feature_interpretation:
            return self._feature_interpretation[feature.identifier]

        return None

    def set_api_context(self, context: Context, /) -> None:
        self._template.set_api_context(context)

    def clear_api_context(self) -> None:
        self._template.clear_api_context()
