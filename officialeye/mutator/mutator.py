import abc
from typing import Dict

# noinspection PyPackageRequirements
import cv2

from officialeye.mutator.config import MutatorConfig


class Mutator(abc.ABC):

    def __init__(self, mutator_id: str, config: Dict[str, any], /):
        super().__init__()

        self.mutator_id = mutator_id

        self._config = MutatorConfig(config, mutator_id)

    def get_config(self) -> MutatorConfig:
        return self._config

    @abc.abstractmethod
    def mutate(self, img: cv2.Mat, /) -> cv2.Mat:
        raise NotImplementedError()
