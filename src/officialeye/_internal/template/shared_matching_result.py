from __future__ import annotations

from abc import ABC
from typing import TYPE_CHECKING, Dict, Iterable, List

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch

# noinspection PyProtectedMember
from officialeye._api.template.matching_result import IMatchingResult
from officialeye._internal.context.singleton import get_internal_afi
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye.error.errors.matching import ErrMatchingMatchCountOutOfBounds

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.template_interface import ITemplate


class SharedMatchingResult(IMatchingResult, ABC):
    """
    This class contains all the logic of the matching result instance, irrespective of whether we use the internal or the external representation.
    The parent process uses the internal representation, whereas the external representation is only for the child process.
    This class represents the aspects that both representations have in common.
    Therefore, it is important that this class operates only on the interface level and is picklable.
    """

    def __init__(self, template: ITemplate, /):
        # keys: keypoint ids
        # values: matches with this keypoint
        self._matches_dict: Dict[str, List[IMatch]] = {}

        for keypoint in template.keypoints:
            self._matches_dict[keypoint.identifier] = []

    def remove_all_matches(self):
        self._matches_dict = {}

    def add_match(self, match: IMatch, /):
        assert match.keypoint.identifier in self._matches_dict
        self._matches_dict[match.keypoint.identifier].append(match)

    def get_all_matches(self) -> Iterable[IMatch]:
        for keypoint_id in self._matches_dict:
            for match in self._matches_dict[keypoint_id]:
                yield match

    def get_total_match_count(self) -> int:
        match_count = 0
        for keypoint_id in self._matches_dict:
            match_count += len(self._matches_dict[keypoint_id])
        return match_count

    def get_keypoint_ids(self) -> Iterable[str]:
        for keypoint_id in self._matches_dict:
            yield keypoint_id

    def get_matches_for_keypoint(self, keypoint_id: str, /) -> Iterable[IMatch]:
        for match in self._matches_dict[keypoint_id]:
            yield match

    def validate(self):

        get_internal_afi().info(Verbosity.DEBUG, "Validating the keypoint matching result.")

        assert len(self._matches_dict) > 0

        total_match_count = 0

        # verify that for every keypoint, it has been matched a number of times that is in the desired bounds
        for keypoint_id in self._matches_dict:
            keypoint = self.template.get_keypoint(keypoint_id)

            keypoint_matches_min = keypoint.matches_min
            keypoint_matches_max = keypoint.matches_max

            keypoint_matches_count = len(self._matches_dict[keypoint_id])

            if keypoint_matches_count < keypoint_matches_min:
                raise ErrMatchingMatchCountOutOfBounds(
                    f"while checking that keypoint '{keypoint_id}' of template '{self.template.identifier}' "
                    f"has been matched a sufficient number of times",
                    f"Expected at least {keypoint_matches_min} matches, got {keypoint_matches_count}"
                )

            if keypoint_matches_count > keypoint_matches_max:

                get_internal_afi().info(
                    Verbosity.INFO_VERBOSE,
                    f"Keypoint '{keypoint_id}' of template '{self.template.identifier}' has too many matches "
                    f"(matches: {keypoint_matches_count} max: {keypoint_matches_max}). Cherry-picking the best matches.")
                # cherry-pick the best matches
                self._matches_dict[keypoint_id] = sorted(self._matches_dict[keypoint_id])[-keypoint_matches_max:]
                keypoint_matches_count = keypoint_matches_max
            else:
                get_internal_afi().info(
                    Verbosity.INFO_VERBOSE,
                    f"Keypoint '{keypoint_id}' of template '{self.template.identifier}' has been matched {keypoint_matches_count} times "
                    f"(min: {keypoint_matches_min} max: {keypoint_matches_max})."
                )

            total_match_count += keypoint_matches_count

        assert total_match_count >= 0
        if total_match_count == 0:
            raise ErrMatchingMatchCountOutOfBounds(
                f"while checking that there has been at least one match for template '{self.template.identifier}'.",
                "There have been no matches."
            )
        elif total_match_count < 3:
            raise ErrMatchingMatchCountOutOfBounds(
                f"while checking that there has been at least three matches for template '{self.template.identifier}'.",
                "There have been less than three matches."
            )
