from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Iterable

from officialeye._api.config import SupervisorConfig
from officialeye._api.template.matching_result import IMatchingResult
from officialeye._api.template.supervision_result import SupervisionResult
from officialeye._api.template.template_interface import ITemplate

if TYPE_CHECKING:
    from officialeye.types import ConfigDict


class ISupervisor(ABC):

    @property
    @abstractmethod
    def config(self) -> SupervisorConfig:
        raise NotImplementedError()

    @abstractmethod
    def setup(self, template: ITemplate, matching_result: IMatchingResult, /) -> None:
        raise NotImplementedError()

    @abstractmethod
    def supervise(self, template: ITemplate, matching_result: IMatchingResult, /) -> Iterable[SupervisionResult]:
        raise NotImplementedError()


class Supervisor(ISupervisor, ABC):

    def __init__(self, supervisor_id: str, config_dict: ConfigDict, /):
        super().__init__()

        self._supervisor_id = supervisor_id
        self._config = SupervisorConfig(config_dict, supervisor_id)

    @property
    def config(self) -> SupervisorConfig:
        return self._config
