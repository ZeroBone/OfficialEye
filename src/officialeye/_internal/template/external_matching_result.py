from __future__ import annotations

from typing import TYPE_CHECKING

from officialeye._internal.api_implementation import IApiInterfaceImplementation
from officialeye._internal.template.external_template import ExternalTemplate
from officialeye._internal.template.shared_matching_result import SharedMatchingResult

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context
    from officialeye._internal.template.internal_matching_result import InternalMatchingResult


class ExternalMatchingResult(SharedMatchingResult, IApiInterfaceImplementation):
    """
    Representation of the matching result, designed to be used by the main process.
    For this reason, it is essential that this class is picklable.
    """

    def __init__(self, internal_matching_result: InternalMatchingResult, external_template: ExternalTemplate, /):
        super().__init__(internal_matching_result.template)

        self._template = external_template

    @property
    def template(self) -> ExternalTemplate:
        return self._template

    def set_api_context(self, context: Context, /) -> None:
        self._template.set_api_context(context)

    def clear_api_context(self) -> None:
        self._template.clear_api_context()
