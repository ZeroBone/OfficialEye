from __future__ import annotations

from typing import Dict, List, Iterable

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch
# noinspection PyProtectedMember
from officialeye._api.template.matcher_result import IMatcherResult
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye._internal.context.singleton import get_internal_context, get_internal_afi
from officialeye.error.errors.matching import ErrMatchingMatchCountOutOfBounds


class InternalMatcherResult(IMatcherResult):

    def __init__(self, template_id: str, /):
        self._template_id = template_id

        # keys: keypoint ids
        # values: matches with this keypoint
        self._matches_dict: Dict[str, List[IMatch]] = {}

        for keypoint in self.template.keypoints:
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

    def get_keypoint_ids(self):
        for keypoint_id in self._matches_dict:
            yield keypoint_id

    def matches_for_keypoint(self, keypoint_id: str, /):
        for match in self._matches_dict[keypoint_id]:
            yield match

    @property
    def template(self):
        return get_internal_context().get_template(self._template_id)

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
                    f"while checking that keypoint '{keypoint_id}' of template '{self._template_id}' "
                    f"has been matched a sufficient number of times",
                    f"Expected at least {keypoint_matches_min} matches, got {keypoint_matches_count}"
                )

            if keypoint_matches_count > keypoint_matches_max:

                get_internal_afi().info(
                    Verbosity.INFO_VERBOSE,
                    f"Keypoint '{keypoint_id}' of template '{self._template_id}' has too many matches "
                    f"(matches: {keypoint_matches_count} max: {keypoint_matches_max}). Cherry-picking the best matches.")
                # cherry-pick the best matches
                self._matches_dict[keypoint_id] = sorted(self._matches_dict[keypoint_id])[:keypoint_matches_max]
                keypoint_matches_count = keypoint_matches_max

            get_internal_afi().info(
                Verbosity.INFO_VERBOSE,
                f"Keypoint '{keypoint_id}' of template '{self._template_id}' has been matched {keypoint_matches_count} times "
                f"(min: {keypoint_matches_min} max: {keypoint_matches_max})."
            )

            total_match_count += keypoint_matches_count

        assert total_match_count >= 0
        if total_match_count == 0:
            raise ErrMatchingMatchCountOutOfBounds(
                f"while checking that there has been at least one match for template '{self._template_id}'.",
                "There have been no matches."
            )

    def debug_print(self):
        get_internal_afi().info(Verbosity.INFO_VERBOSE, f"Found {self.get_total_match_count()} matches!")
