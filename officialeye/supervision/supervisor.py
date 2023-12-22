import abc
import random
from abc import ABC
from typing import List, Union

import click

from officialeye.context.singleton import oe_context
from officialeye.debug.debuggable import Debuggable
from officialeye.supervision.result import SupervisionResult
from officialeye.match.result import KeypointMatchingResult


_SUPERVISION_RESULT_FIRST = "first"
_SUPERVISION_RESULT_RANDOM = "random"
_SUPERVISION_RESULT_BEST_MSE = "best_mse"
_SUPERVISION_RESULT_BEST_SCORE = "best_score"


class Supervisor(ABC, Debuggable):

    def __init__(self, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__()

        self.template_id = template_id
        self._kmr = kmr

        self._delta_x = oe_context().get_template(self.template_id).width // 2
        self._delta_y = oe_context().get_template(self.template_id).height // 2

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Total match count: {self._kmr.get_total_match_count()}", fg="yellow")

    def get_template(self):
        return oe_context().get_template(self.template_id)

    @abc.abstractmethod
    def _run(self) -> List[SupervisionResult]:
        raise NotImplementedError()

    def _run_first(self) -> Union[SupervisionResult, None]:
        results = self._run()
        return None if len(results) == 0 else results[0]

    def _run_random(self) -> Union[SupervisionResult, None]:
        results = self._run()
        return None if len(results) == 0 else results[random.randint(0, len(results) - 1)]

    def _run_best_mse(self) -> Union[SupervisionResult, None]:
        results = self._run()

        if len(results) == 0:
            return None

        best_result = results[0]
        best_result_mse = best_result.get_weighted_mse()

        for result_id, result in enumerate(results):
            result_mse = result.get_weighted_mse()

            if self.in_debug_mode() and not oe_context().quiet_mode and oe_context().verbose_mode:
                click.secho(f"Result #{result_id + 1} has MSE {result_mse}", fg="yellow")

            if result_mse < best_result_mse:
                best_result_mse = result_mse
                best_result = result

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Best result has MSE {best_result_mse}", fg="yellow")

        return best_result

    def _run_best_score(self) -> Union[SupervisionResult, None]:

        results = self._run()

        if len(results) == 0:
            return None

        best_result = results[0]
        best_result_score = best_result.get_score()
        best_result_mse = best_result.get_weighted_mse()

        for result_id, result in enumerate(results):
            result_score = result.get_score()

            if self.in_debug_mode() and not oe_context().quiet_mode and oe_context().verbose_mode:
                click.secho(f"Result #{result_id + 1} has score {result_score}", fg="yellow")

            if result_score > best_result_score:
                best_result_score = result_score
                best_result_mse = result.get_weighted_mse()
                best_result = result
            elif result_score == best_result_score:
                current_result_mse = result.get_weighted_mse()
                if current_result_mse < best_result_mse:
                    best_result_mse = current_result_mse
                    best_result = result

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Best result has score {best_result_score} and MSE {best_result_mse}", fg="yellow")

        return best_result

    def run(self) -> Union[SupervisionResult, None]:

        supervision_result_choice_engine = self.get_template().get_supervision_result()

        if self.in_debug_mode() and not oe_context().quiet_mode:
            click.secho(f"Applying '{supervision_result_choice_engine}' supervision result choice engine.", fg="yellow")

        if supervision_result_choice_engine == _SUPERVISION_RESULT_FIRST:
            return self._run_first()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_RANDOM:
            return self._run_random()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_MSE:
            return self._run_best_mse()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_SCORE:
            return self._run_best_score()

        assert False, "Invalid supervision result"
