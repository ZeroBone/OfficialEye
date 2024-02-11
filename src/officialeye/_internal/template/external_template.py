from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Iterable, List

# noinspection PyProtectedMember
from officialeye._api.future import Future

# noinspection PyProtectedMember
from officialeye._api.image import IImage, Image

# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate
from officialeye._internal.api.detect import template_detect
from officialeye._internal.api_implementation import IApiInterfaceImplementation

# noinspection PyProtectedMember
from officialeye._internal.template.external_feature import ExternalFeature
from officialeye._internal.template.keypoint import ExternalKeypoint
from officialeye.error.errors.general import ErrOperationNotSupported

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.context import Context

    # noinspection PyProtectedMember
    from officialeye._api.template.supervision_result import ISupervisionResult
    from officialeye._internal.template.internal_template import InternalTemplate


class ExternalTemplate(ITemplate, IApiInterfaceImplementation):
    """
    Representation of a template instance designed to be shared between processes.
    It is very important that this class is picklable!
    """

    def __init__(self, template: InternalTemplate, /):
        super().__init__()

        self._context: Context | None = None

        self._identifier: str = template.identifier
        self._name: str = template.name
        self._path: str = template.get_path()
        self._source_image_path: str = template.get_source_image_path()

        self._width = template.width
        self._height = template.height

        self._keypoints: Dict[str, ExternalKeypoint] = {}
        self._features: Dict[str, ExternalFeature] = {}

        for keypoint in template.keypoints:
            self._keypoints[keypoint.identifier] = ExternalKeypoint(keypoint, self)

        for feature in template.features:
            self._features[feature.identifier] = ExternalFeature(feature, self)

        self._source_mutators: List[IMutator] = [
            mutator for mutator in template.get_source_mutators()
        ]

        self._target_mutators: List[IMutator] = [
            mutator for mutator in template.get_target_mutators()
        ]

    def set_api_context(self, context: Context, /) -> None:
        self._context = context

        for external_keypoint in self.keypoints:
            external_keypoint.set_api_context(context)

        for external_feature in self.features:
            external_feature.set_api_context(context)

    def clear_api_context(self) -> None:
        self._context = None

        for external_keypoint in self.keypoints:
            external_keypoint.clear_api_context()

        for external_feature in self.features:
            external_feature.clear_api_context()

    def load(self) -> None:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

    def detect_async(self, /, *, target: IImage) -> Future:

        # TODO: this is hacky, maybe use a more clean approach here?
        assert isinstance(target, Image)

        # noinspection PyProtectedMember
        return self._context._submit_task(
            template_detect,
            f"Detecting [b]{self._name}[/]...",
            self._path,
            target_path=target._path,
        )

    def detect(self, /, **kwargs) -> ISupervisionResult:
        future = self.detect_async(**kwargs)
        return future.result()

    def get_image(self) -> IImage:
        return Image(self._context, path=self._source_image_path)

    def get_mutated_image(self) -> IImage:
        img = self.get_image()
        img.apply_mutators(*self._source_mutators)
        return img

    @property
    def identifier(self) -> str:
        return self._identifier

    @property
    def name(self) -> str:
        return self._name

    @property
    def width(self) -> int:
        return self._width

    @property
    def height(self) -> int:
        return self._height

    @property
    def keypoints(self) -> Iterable[ExternalKeypoint]:
        return self._keypoints.values()

    @property
    def features(self) -> Iterable[ExternalFeature]:
        return self._features.values()

    def get_feature(self, feature_id: str, /) -> ExternalFeature | None:
        if feature_id not in self._features:
            return None
        return self._features[feature_id]

    def get_keypoint(self, keypoint_id: str, /) -> ExternalKeypoint | None:
        if keypoint_id not in self._keypoints:
            return None
        return self._keypoints[keypoint_id]
