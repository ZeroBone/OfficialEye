import abc
from abc import ABC
from typing import List, Union

import click

from officialeye.context.singleton import oe_context
from officialeye.debug.debuggable import Debuggable
from officialeye.supervision.result import SupervisionResult
from officialeye.match.result import KeypointMatchingResult


class Supervisor(ABC, Debuggable):

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__()

        self.template_id = template_id
        self._kmr = kmr

        self._delta_x = oe_context().get_template(self.template_id).width // 2
        self._delta_y = oe_context().get_template(self.template_id).height // 2

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Total match count: {self._kmr.get_total_match_count()}", fg="yellow")

    @abc.abstractmethod
    def _run(self) -> List[SupervisionResult]:
        raise NotImplementedError()

    def run(self) -> Union[SupervisionResult, None]:
        results = self._run()

        if len(results) == 0:
            return None

        best_result = results[0]
        best_result_mse = best_result.get_mse()

        for result in results:
            result_mse = result.get_mse()
            if result_mse < best_result_mse:
                best_result_mse = result_mse
                best_result = result

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Best result has MSE {best_result_mse}", fg="yellow")

        return best_result
