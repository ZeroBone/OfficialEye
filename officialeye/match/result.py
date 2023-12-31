from typing import List, Dict

from officialeye.context.singleton import oe_context
from officialeye.error.errors.matching import ErrMatchingMatchCountOutOfBounds
from officialeye.match.match import Match
from officialeye.util.logger import oe_debug, oe_debug_verbose


class KeypointMatchingResult:

    def __init__(self, template_id: str, /):
        self._template_id = template_id
        # keys: keypoint ids
        # values: matches with this keypoint
        self._matches_dict: Dict[str, List[Match]] = {}

    def remove_all_matches(self):
        self._matches_dict = {}

    def add_match(self, match: Match, /):
        if match.keypoint_id not in self._matches_dict:
            self._matches_dict[match.keypoint_id] = []
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
        return oe_context().get_template(self._template_id)

    def validate(self):

        oe_debug("Validating the keypoint matching result.")

        # verify that for every keypoint, it has been matched a number of times that is in the desired bounds
        for keypoint_id in self._matches_dict:
            keypoint = self.get_template().get_keypoint(keypoint_id)

            keypoint_matches_min = keypoint.get_matches_min()
            keypoint_matches_max = keypoint.get_matches_max()

            keypoint_matches_count = len(self._matches_dict[keypoint_id])

            if keypoint_matches_count < keypoint_matches_min:
                raise ErrMatchingMatchCountOutOfBounds(
                    f"keypoint '{keypoint_id}' of template '{self._template_id}' was match an incorrect number of times",
                    f"expected at least {keypoint_matches_min} matches, got {keypoint_matches_count}"
                )

            if keypoint_matches_count > keypoint_matches_max:
                oe_debug(f"Keypoint '{keypoint_id}' of template '{self._template_id}' has too many matches "
                         f"(matches: {keypoint_matches_count} max: {keypoint_matches_max}). Cherry-picking the best matches.")
                # cherry-pick the best matches
                self._matches_dict[keypoint_id] = sorted(self._matches_dict[keypoint_id])[:keypoint_matches_max]
                keypoint_matches_count = keypoint_matches_max

            oe_debug(f"Keypoint '{keypoint_id}' of template '{self._template_id}' has been matched {keypoint_matches_count} times "
                     f"(min: {keypoint_matches_min} max: {keypoint_matches_max}).")

    def debug_print(self):
        oe_debug(f"Found {self.get_total_match_count()} matched points!")

        oe_debug_verbose(f"Listing matched points:")
        for match in self.get_matches():
            oe_debug_verbose(f"> {match}")

