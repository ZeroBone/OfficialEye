from __future__ import annotations

from concurrent.futures import Future
from typing import Iterable, Dict, TYPE_CHECKING

# noinspection PyProtectedMember
from officialeye._api.image import IImage
# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate
# noinspection PyProtectedMember
from officialeye._internal.template.feature import ExternalFeature
from officialeye._internal.template.keypoint import ExternalKeypoint
from officialeye.error.errors.general import ErrOperationNotSupported


if TYPE_CHECKING:
    from officialeye._internal.template.internal_template import InternalTemplate
    # noinspection PyProtectedMember
    from officialeye._api.template.supervision_result import SupervisionResult


class ExternalTemplate(ITemplate):
    """
    Representation of a template instance designed to be shared between processes.
    It is very important that this class is picklable!
    """

    def __init__(self, template: InternalTemplate, /):
        super().__init__()

        self._identifier: str = template.identifier
        self._name: str = template.name
        self._width = template.width
        self._height = template.height

        self._keypoints: Dict[str, ExternalKeypoint] = {}
        self._features: Dict[str, ExternalFeature] = {}

        for keypoint in template.keypoints:
            self._keypoints[keypoint.identifier] = ExternalKeypoint(keypoint, self)

        for feature in template.features:
            self._features[feature.identifier] = ExternalFeature(feature, self)

    def load(self) -> None:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

    def detect_async(self, /, *, target: IImage) -> Future:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

    def detect(self, /, **kwargs) -> SupervisionResult:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

    def get_image(self) -> IImage:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

    def get_mutated_image(self) -> IImage:
        raise ErrOperationNotSupported(
            "while accessing an external template instance.",
            "The way in which it was accessed is not supported."
        )

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
