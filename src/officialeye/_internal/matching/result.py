from typing import List, Dict

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.matching import ErrMatchingMatchCountOutOfBounds
from officialeye._internal.logger.singleton import get_logger
from officialeye._internal.matching.match import Match


class MatchingResult:

    def __init__(self, context: Context, template_id: str, /):
        self._context = context
        self._template_id = template_id

        # keys: keypoint ids
        # values: matches with this keypoint
        self._matches_dict: Dict[str, List[Match]] = {}

        for keypoint in self.get_template().keypoints():
            self._matches_dict[keypoint.region_id] = []

    def remove_all_matches(self):
        self._matches_dict = {}

    def add_match(self, match: Match, /):
        assert match.keypoint_id in self._matches_dict
        self._matches_dict[match.keypoint_id].append(match)

    def get_matches(self):
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

    def get_template(self):
        return self._context.get_template(self._template_id)

    def validate(self):

        get_logger().debug("Validating the keypoint matching result.")

        assert len(self._matches_dict) > 0

        total_match_count = 0

        # verify that for every keypoint, it has been matched a number of times that is in the desired bounds
        for keypoint_id in self._matches_dict:
            keypoint = self.get_template().get_keypoint(keypoint_id)

            keypoint_matches_min = keypoint.get_matches_min()
            keypoint_matches_max = keypoint.get_matches_max()

            keypoint_matches_count = len(self._matches_dict[keypoint_id])

            if keypoint_matches_count < keypoint_matches_min:
                raise ErrMatchingMatchCountOutOfBounds(
                    f"while checking that keypoint '{keypoint_id}' of template '{self._template_id}' "
                    f"has been matched a sufficient number of times",
                    f"Expected at least {keypoint_matches_min} matches, got {keypoint_matches_count}"
                )

            if keypoint_matches_count > keypoint_matches_max:
                get_logger().debug(
                    f"Keypoint '{keypoint_id}' of template '{self._template_id}' has too many matches "
                    f"(matches: {keypoint_matches_count} max: {keypoint_matches_max}). Cherry-picking the best matches.")
                # cherry-pick the best matches
                self._matches_dict[keypoint_id] = sorted(self._matches_dict[keypoint_id])[:keypoint_matches_max]
                keypoint_matches_count = keypoint_matches_max

            get_logger().debug(f"Keypoint '{keypoint_id}' of template '{self._template_id}' has been matched {keypoint_matches_count} times "
                               f"(min: {keypoint_matches_min} max: {keypoint_matches_max}).")

            total_match_count += keypoint_matches_count

        assert total_match_count >= 0
        if total_match_count == 0:
            raise ErrMatchingMatchCountOutOfBounds(
                f"while checking that there has been at least one match for template '{self._template_id}'.",
                f"There have been no matches."
            )

    def debug_print(self):
        get_logger().debug(f"Found {self.get_total_match_count()} matched points!")

        get_logger().debug_verbose(f"Listing matched points:")
        for match in self.get_matches():
            get_logger().debug_verbose(f"> {match}")
