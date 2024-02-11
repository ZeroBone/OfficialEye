from __future__ import annotations

from typing import TYPE_CHECKING, Iterable, List

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature
from officialeye._internal.api_implementation import IApiInterfaceImplementation
from officialeye._internal.template.region import ExternalRegion

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context

    # noinspection PyProtectedMember
    from officialeye._api.mutator import IMutator
    from officialeye._internal.template.external_template import ExternalTemplate
    from officialeye._internal.template.internal_feature import InternalFeature


class ExternalFeature(ExternalRegion, IFeature, IApiInterfaceImplementation):

    def __init__(self, internal_feature: InternalFeature, external_template: ExternalTemplate, /):
        super().__init__(internal_feature, external_template)

        self._mutators: List[IMutator] = list(internal_feature.get_mutators())

    def get_mutators(self) -> Iterable[IMutator]:
        return self._mutators

    def set_api_context(self, context: Context, /) -> None:
        # no methods of this class require any contextual information to work, nothing to do
        pass

    def clear_api_context(self) -> None:
        # no methods of this class require any contextual information to work, nothing to do
        pass
