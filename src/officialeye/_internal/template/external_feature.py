from __future__ import annotations

from typing import TYPE_CHECKING

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature
from officialeye._internal.api_implementation import IApiInterfaceImplementation
from officialeye._internal.template.region import ExternalRegion


if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context
    from officialeye._internal.template.internal_feature import InternalFeature
    from officialeye._internal.template.external_template import ExternalTemplate


class ExternalFeature(ExternalRegion, IFeature, IApiInterfaceImplementation):

    def __init__(self, internal_feature: InternalFeature, external_template: ExternalTemplate, /):
        super().__init__(internal_feature, external_template)

    def set_api_context(self, context: Context, /):
        # no methods of this class require any contextual information to work, nothing to do
        pass
