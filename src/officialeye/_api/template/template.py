from __future__ import annotations

from concurrent.futures import Future
from typing import TYPE_CHECKING, Iterable

from officialeye._api.template.feature import Feature
from officialeye._api.template.keypoint import Keypoint
from officialeye._api.analysis_result import AnalysisResult
from officialeye._api.image import IImage, Image
from officialeye._api.template.template_interface import ITemplate
# noinspection PyProtectedMember
from officialeye._internal.api import template_load, template_analyze
# noinspection PyProtectedMember
from officialeye._internal.template.template_data import TemplateData

if TYPE_CHECKING:
    from officialeye._api.context import Context
    from officialeye._api.template.feature import IFeature
    from officialeye._api.template.keypoint import IKeypoint


class Template(ITemplate):

    def __init__(self, context: Context, /, *, path: str):
        super().__init__()

        self._context = context
        self._path = path

        self._data: TemplateData | None = None

    def load(self):
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        if self._data is not None:
            # data has already been loaded, nothing to do
            return

        # noinspection PyProtectedMember
        future = self._context._submit_task(template_load, "Loading template...", self._path)

        self._data = future.result()

        assert self._data is not None

    # noinspection PyProtectedMember
    def analyze_async(self, /, *, target: IImage, interpretation_target: IImage | None = None) -> Future:

        assert isinstance(target, Image)
        assert interpretation_target is None or isinstance(interpretation_target, Image)

        return self._context._submit_task(
            template_analyze,
            "Running analysis...",
            self._path,
            target_path=target._path,
            interpretation_target_path=None if interpretation_target is None else interpretation_target._path
        )

    def analyze(self, /, **kwargs) -> AnalysisResult:
        future = self.analyze_async(**kwargs)
        return future.result()

    def get_image(self) -> Image:
        self.load()
        return Image(self._context, path=self._data.source)

    def get_mutated_image(self) -> Image:
        img = self.get_image()
        img.apply_mutators(*self._data.source_mutators)
        return img

    @property
    def identifier(self) -> str:
        self.load()
        return self._data.identifier

    @property
    def name(self) -> str:
        self.load()
        return self._data.name

    @property
    def width(self) -> int:
        self.load()
        return self._data.width

    @property
    def height(self) -> int:
        self.load()
        return self._data.height

    @property
    def keypoints(self) -> Iterable[IKeypoint]:
        self.load()
        return frozenset(Keypoint(self, **keypoint.get_init_args()) for keypoint in self._data.keypoints)

    @property
    def features(self) -> Iterable[IFeature]:
        self.load()
        return frozenset(Feature(self, **feature.get_init_args()) for feature in self._data.features)
