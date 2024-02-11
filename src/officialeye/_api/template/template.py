from __future__ import annotations

from concurrent.futures import Future
from typing import TYPE_CHECKING, Iterable

from officialeye._api.image import IImage
from officialeye._api.template.template_interface import ITemplate

# noinspection PyProtectedMember
from officialeye._internal.api.load import template_load

# noinspection PyProtectedMember
from officialeye._internal.template.external_template import ExternalTemplate

if TYPE_CHECKING:
    from officialeye._api.context import Context
    from officialeye._api.template.feature import IFeature
    from officialeye._api.template.keypoint import IKeypoint
    from officialeye._api.template.supervision_result import ISupervisionResult


class Template(ITemplate):

    def __init__(self, context: Context, /, *, path: str):
        super().__init__()

        self._context = context
        self._path = path

        # None indicates that the template has not yet been loaded
        self._external_template: ExternalTemplate | None = None

    def load(self) -> None:
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        if self._external_template is not None:
            # the template has already been loaded, nothing to do
            return

        # noinspection PyProtectedMember
        future = self._context._submit_task(template_load, "Loading template...", self._path)

        self._external_template = future.result()

        assert self._external_template is not None
        assert isinstance(self._external_template, ExternalTemplate)

    def detect_async(self, /, *, target: IImage) -> Future:
        self.load()
        return self._external_template.detect_async(target=target)

    def detect(self, /, **kwargs) -> ISupervisionResult:
        self.load()
        return self._external_template.detect(**kwargs)

    def get_image(self) -> IImage:
        self.load()
        return self._external_template.get_image()

    def get_mutated_image(self) -> IImage:
        self.load()
        return self._external_template.get_mutated_image()

    @property
    def identifier(self) -> str:
        self.load()
        return self._external_template.identifier

    @property
    def name(self) -> str:
        self.load()
        return self._external_template.name

    @property
    def width(self) -> int:
        self.load()
        return self._external_template.width

    @property
    def height(self) -> int:
        self.load()
        return self._external_template.height

    @property
    def keypoints(self) -> Iterable[IKeypoint]:
        self.load()
        return self._external_template.keypoints

    @property
    def features(self) -> Iterable[IFeature]:
        self.load()
        return self._external_template.features

    def get_feature(self, feature_id: str, /) -> IFeature | None:
        self.load()
        return self._external_template.get_feature(feature_id)

    def get_keypoint(self, keypoint_id: str, /) -> IKeypoint | None:
        self.load()
        return self._external_template.get_keypoint(keypoint_id)
