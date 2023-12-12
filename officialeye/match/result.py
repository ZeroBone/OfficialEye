from typing import List, Dict

import click

from officialeye.match.match import Match


class KeypointMatchingResult:

    def __init__(self):
        # keys: template ids
        # values: matches with this template id
        self._matches_dict: Dict[str, List[Match]] = {}

    def add_match(self, match: Match, /):
        if match.keypoint_id not in self._matches_dict:
            self._matches_dict[match.keypoint_id] = []
        self._matches_dict[match.keypoint_id].append(match)

    def get_matches(self):
        for template_id in self._matches_dict:
            for match in self._matches_dict[template_id]:
                yield match

    def get_total_match_count(self) -> int:
        match_count = 0
        for template_id in self._matches_dict:
            match_count += len(self._matches_dict[template_id])
        return match_count

    def get_template_ids(self):
        for template_id in self._matches_dict:
            yield template_id

    def matches_for_template(self, template_id: str, /):
        for match in self._matches_dict[template_id]:
            yield match

    def debug_print(self):
        click.echo(f"Listing all matched points:")
        for match in self.get_matches():
            click.echo(f"> {match}")

