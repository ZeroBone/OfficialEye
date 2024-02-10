from __future__ import annotations

from concurrent.futures import Future
from typing import TYPE_CHECKING, Iterable, Dict, List

from officialeye._api.template.supervision_result import SupervisionResult
from officialeye._api.mutator import IMutator
from officialeye._api.template.feature import Feature
from officialeye._api.template.keypoint import Keypoint
from officialeye._api.image import IImage, Image
from officialeye._api.template.template_interface import ITemplate
# noinspection PyProtectedMember
from officialeye._internal.api import template_load, template_detect

if TYPE_CHECKING:
    from officialeye._api.context import Context
    from officialeye._api.template.feature import IFeature
    from officialeye._api.template.keypoint import IKeypoint
    # noinspection PyProtectedMember
    from officialeye._internal.template.external_template import ExternalTemplate


class Template(ITemplate):

    def __init__(self, context: Context, /, *, path: str):
        super().__init__()

        self._context = context
        self._path = path

        self._loaded: bool = False

        self._identifier: str | None = None
        self._name: str | None = None
        self._source: str | None = None

        self._width: int | None = None
        self._height: int | None = None

        self._features: Dict[str, Feature] = {}
        self._keypoints: Dict[str, Keypoint] = {}

        self._source_mutators: List[IMutator] | None = None
        self._target_mutators: List[IMutator] | None = None

    def load(self) -> None:
        """
        Loads the template into memory for further processing.

        If you prefer lazy-evaluation, do not call this method.
        Instead, run the desired operations with the template, and the necessary resources will be loaded on-the-fly.
        Use this method only if you really want to preload the template.
        """

        if self._loaded:
            # data has already been loaded, nothing to do
            return

        # noinspection PyProtectedMember
        future = self._context._submit_task(template_load, "Loading template...", self._path)

        _data: ExternalTemplate = future.result()
        assert _data is not None

        self._identifier = _data.identifier
        self._name = _data.name
        self._source = _data.source
        assert self._identifier is not None
        assert self._name is not None
        assert self._source is not None

        self._width = _data.width
        self._height = _data.height
        assert self._width is not None
        assert self._height is not None

        for feature in _data.features:
            self._features[feature.identifier] = Feature(self, **feature.get_init_args())

        for keypoint in _data.keypoints:
            self._keypoints[keypoint.identifier] = Keypoint(self, **keypoint.get_init_args())

        self._source_mutators = _data.source_mutators
        self._target_mutators = _data.target_mutators
        assert self._source_mutators is not None
        assert self._target_mutators is not None

        self._loaded = True

    def detect_async(self, /, *, target: IImage) -> Future:

        assert isinstance(target, Image)

        # noinspection PyProtectedMember
        return self._context._submit_task(
            template_detect,
            "Running analysis...",
            self._path,
            target_path=target._path,
        )

    def detect(self, /, **kwargs) -> SupervisionResult:
        future = self.detect_async(**kwargs)
        return future.result()

    def get_image(self) -> Image:
        self.load()
        return Image(self._context, path=self._source)

    def get_mutated_image(self) -> Image:
        img = self.get_image()
        img.apply_mutators(*self._source_mutators)
        return img

    @property
    def identifier(self) -> str:
        self.load()
        return self._identifier

    @property
    def name(self) -> str:
        self.load()
        return self._name

    @property
    def width(self) -> int:
        self.load()
        return self._width

    @property
    def height(self) -> int:
        self.load()
        return self._height

    @property
    def keypoints(self) -> Iterable[IKeypoint]:
        self.load()
        for keypoint_id in self._keypoints:
            yield self._keypoints[keypoint_id]

    @property
    def features(self) -> Iterable[IFeature]:
        self.load()
        for feature_id in self._features:
            yield self._features[feature_id]

    def get_feature(self, feature_id: str, /) -> IFeature | None:

        if feature_id not in self._features:
            return None

        return self._features[feature_id]

    def get_keypoint(self, keypoint_id: str, /) -> IKeypoint | None:

        if keypoint_id not in self._keypoints:
            return None

        return self._keypoints[keypoint_id]
