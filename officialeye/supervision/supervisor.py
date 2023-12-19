import abc
from abc import ABC
from typing import Union

import click

from officialeye.context.singleton import oe_context
from officialeye.debug.container import DebugContainer
from officialeye.debug.debuggable import Debuggable
from officialeye.supervision.result import SupervisionResult
from officialeye.match.result import KeypointMatchingResult


class Supervisor(ABC, Debuggable):

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /, *,
                 debug: DebugContainer = None):
        super().__init__(debug=debug)

        self.template_id = template_id
        self._kmr = kmr

        self._delta_x = oe_context().get_template(self.template_id).width // 2
        self._delta_y = oe_context().get_template(self.template_id).height // 2

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Total match count: {self._kmr.get_total_match_count()}", fg="yellow")

    @abc.abstractmethod
    def run(self) -> Union[SupervisionResult, None]:
        raise NotImplementedError()
