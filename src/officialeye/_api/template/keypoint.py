from abc import ABC, abstractmethod

from officialeye._api.template.region import IRegion


class IKeypoint(IRegion, ABC):

    @property
    @abstractmethod
    def matches_min(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def matches_max(self) -> int:
        raise NotImplementedError()

    def __str__(self) -> str:
        return f"Keypoint '{self.identifier}'"
