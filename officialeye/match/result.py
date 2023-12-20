from typing import List, Dict

import click

from officialeye.context.singleton import oe_context
from officialeye.match.match import Match


class KeypointMatchingResult:

    def __init__(self):
        # keys: keypoint ids
        # values: matches with this template id
        self._matches_dict: Dict[str, List[Match]] = {}

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

    def debug_print(self):
        if oe_context().quiet_mode:
            return
        click.secho(f"Found {self.get_total_match_count()} matched points!", fg="yellow")

        if oe_context().verbose_mode:
            click.secho(f"Listing matched points:", fg="yellow")
            for match in self.get_matches():
                click.secho(f"> {match}", fg="yellow")

