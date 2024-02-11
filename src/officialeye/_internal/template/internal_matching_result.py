from __future__ import annotations

from typing import TYPE_CHECKING, Dict, List

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch
from officialeye._internal.context.singleton import get_internal_context
from officialeye._internal.template.shared_matching_result import SharedMatchingResult

if TYPE_CHECKING:
    from officialeye._internal.template.internal_template import InternalTemplate


class InternalMatchingResult(SharedMatchingResult):
    """
    Representation of the matching result, designed to be used by the child process only.
    """

    def __init__(self, template: InternalTemplate, /):
        super().__init__(template)

        self._template_id = template.identifier

        # keys: keypoint ids
        # values: matches with this keypoint
        self._matches_dict: Dict[str, List[IMatch]] = {}

        for keypoint in self.template.keypoints:
            self._matches_dict[keypoint.identifier] = []

    @property
    def template(self) -> InternalTemplate:
        return get_internal_context().get_template(self._template_id)
