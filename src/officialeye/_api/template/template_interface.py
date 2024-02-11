from abc import ABC, abstractmethod
from typing import Any, Iterable

from officialeye._api.future import Future
from officialeye._api.image import IImage
from officialeye._api.template.feature import IFeature
from officialeye._api.template.keypoint import IKeypoint
from officialeye._api.template.supervision_result import ISupervisionResult


class ITemplate(ABC):

    def __init__(self):
        super().__init__()

    @abstractmethod
    def load(self) -> None:
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        raise NotImplementedError()

    @abstractmethod
    def detect_async(self, /, *, target: IImage) -> Future:
        raise NotImplementedError()

    @abstractmethod
    def detect(self, /, **kwargs) -> ISupervisionResult:
        raise NotImplementedError()

    @abstractmethod
    def get_image(self) -> IImage:
        raise NotImplementedError()

    @abstractmethod
    def get_mutated_image(self) -> IImage:
        raise NotImplementedError()

    @property
    @abstractmethod
    def identifier(self) -> str:
        raise NotImplementedError()

    @property
    @abstractmethod
    def name(self) -> str:
        raise NotImplementedError()

    @property
    @abstractmethod
    def width(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def height(self) -> int:
        raise NotImplementedError()

    @property
    @abstractmethod
    def keypoints(self) -> Iterable[IKeypoint]:
        raise NotImplementedError()

    @property
    @abstractmethod
    def features(self) -> Iterable[IFeature]:
        raise NotImplementedError()

    @abstractmethod
    def get_feature(self, feature_id: str, /) -> IFeature | None:
        raise NotImplementedError()

    @abstractmethod
    def get_keypoint(self, keypoint_id: str, /) -> IKeypoint | None:
        raise NotImplementedError()

    def __str__(self) -> str:
        return f"Template '{self.identifier}'."

    def __eq__(self, o: Any) -> bool:

        if not isinstance(o, ITemplate):
            return False

        return self.identifier == o.identifier

    def __hash__(self):
        return hash(self.identifier)
