from abc import ABC, abstractmethod

from officialeye._api.template.template_interface import ITemplate
from officialeye._api.config import SupervisorConfig


class ISupervisor(ABC):

    @property
    @abstractmethod
    def config(self) -> SupervisorConfig:
        raise NotImplementedError()

    @abstractmethod
    def setup(self, template: ITemplate, matching_result, /) -> None:
        raise NotImplementedError()
