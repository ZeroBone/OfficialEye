from abc import abstractmethod, ABC
from concurrent.futures import Future
from typing import Iterable

from officialeye._api.template.keypoint import IKeypoint
from officialeye._api.template.feature import IFeature
from officialeye._api.analysis_result import AnalysisResult
from officialeye._api.image import IImage


class ITemplate(ABC):

    def __init__(self):
        super().__init__()

    @abstractmethod
    def load(self):
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        raise NotImplementedError()

    @abstractmethod
    def analyze_async(self, /, *, target: IImage, interpretation_target: IImage | None = None) -> Future:
        raise NotImplementedError()

    @abstractmethod
    def analyze(self, /, **kwargs) -> AnalysisResult:
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
