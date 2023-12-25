import abc
import random
from abc import ABC
from typing import List, Union

from officialeye.context.singleton import oe_context
from officialeye.debug.debuggable import Debuggable
from officialeye.match.result import KeypointMatchingResult
from officialeye.supervision.result import SupervisionResult
from officialeye.utils.logger import oe_debug, oe_debug_verbose, oe_warn

_SUPERVISION_RESULT_FIRST = "first"
_SUPERVISION_RESULT_RANDOM = "random"
_SUPERVISION_RESULT_BEST_MSE = "best_mse"
_SUPERVISION_RESULT_BEST_SCORE = "best_score"


class Supervisor(ABC, Debuggable):

    def __init__(self, engine_id: str, template_id: str, kmr: KeypointMatchingResult, /):
        super().__init__()

        self.__engine_id = engine_id
        self.__default_config = None

        # whether or not the user has been warned that the configuration file does not contain supervision engine specific configuration
        # and that thererefore the default settings have been applied
        self.__warned_about_config_fallback = False

        self.template_id = template_id
        self._kmr = kmr

        self._delta_x = oe_context().get_template(self.template_id).width // 2
        self._delta_y = oe_context().get_template(self.template_id).height // 2

        oe_debug(f"Total match count: {self._kmr.get_total_match_count()}")

    def _set_default_config(self, default_config: dict):
        self.__default_config = default_config

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

            oe_debug_verbose(f"Result #{result_id + 1} has MSE {result_mse}")

            if result_mse < best_result_mse:
                best_result_mse = result_mse
                best_result = result

        oe_debug(f"Best result has MSE {best_result_mse}", fg="yellow")

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

            oe_debug_verbose(f"Result #{result_id + 1} has score {result_score}")

            if result_score > best_result_score:
                best_result_score = result_score
                best_result_mse = result.get_weighted_mse()
                best_result = result
            elif result_score == best_result_score:
                current_result_mse = result.get_weighted_mse()
                if current_result_mse < best_result_mse:
                    best_result_mse = current_result_mse
                    best_result = result

        oe_debug(f"Best result has score {best_result_score} and MSE {best_result_mse}")

        return best_result

    def get_config(self) -> dict:

        assert self.__default_config is not None, "get_config() should not be called if there is no default configuration configured"

        supervision_config = self.get_template().get_supervision_config()

        if self.__engine_id in supervision_config:
            return supervision_config[self.__engine_id]

        # there is no supervision engine specific configuration available
        # therefore, we need to fallback to the default configuration

        if not self.__warned_about_config_fallback:
            self.__warned_about_config_fallback = True
            oe_warn(f"Template '{self.template_id}' does not contain supervision configuration for the '{self.__engine_id}' engine."
                    f" Therefore, the default configuration had to be applied.")

        return self.__default_config

    def run(self) -> Union[SupervisionResult, None]:

        assert self.__default_config is not None, "Default supervision configuration has not been configured"

        supervision_result_choice_engine = self.get_template().get_supervision_result()

        oe_debug(f"Applying '{supervision_result_choice_engine}' supervision result choice engine.")

        if supervision_result_choice_engine == _SUPERVISION_RESULT_FIRST:
            return self._run_first()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_RANDOM:
            return self._run_random()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_MSE:
            return self._run_best_mse()

        if supervision_result_choice_engine == _SUPERVISION_RESULT_BEST_SCORE:
            return self._run_best_score()

        assert False, "Invalid supervision result"
