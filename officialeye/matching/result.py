from typing import List

import click

from officialeye.matching.match import Match


class KeypointMatchingResult:

    def __init__(self):
        self.matches: List[Match] = []

    def add_match(self, match: Match, /):
        self.matches.append(match)

    def __str__(self):
        return ", ".join(("{%s, %s}" % (p1, p2) for p1, p2 in self.matches))

    def debug_print(self):
        click.echo(f"Listing all matched points:")
        for match in self.matches:
            click.echo(f"> {match}")

