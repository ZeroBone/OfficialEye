from __future__ import annotations

import os
from concurrent.futures import Future
from typing import Dict, List, TYPE_CHECKING, Iterable

import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.image import IImage
# noinspection PyProtectedMember
from officialeye._api.template.template import ITemplate
# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye._internal.context.singleton import get_internal_context, get_internal_afi
from officialeye._internal.template.image import InternalImage
from officialeye._internal.template.utils import load_mutator_from_dict
from officialeye._internal.timer import Timer
from officialeye.error.errors.general import ErrOperationNotSupported
from officialeye.error.errors.io import ErrIOInvalidPath
from officialeye.error.errors.template import (
    ErrTemplateInvalidFeature,
    ErrTemplateInvalidKeypoint,
    ErrTemplateInvalidSupervisionEngine,
)

from officialeye._internal.matching.result import MatchingResult
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.supervision.supervisors.combinatorial import CombinatorialSupervisor
from officialeye._internal.supervision.supervisors.least_squares_regression import LeastSquaresRegressionSupervisor
from officialeye._internal.supervision.supervisors.orthogonal_regression import OrthogonalRegressionSupervisor
from officialeye._internal.supervision.visualizer import SupervisionResultVisualizer
from officialeye._internal.template.feature_class.loader import load_template_feature_classes
from officialeye._internal.template.feature_class.manager import FeatureClassManager
from officialeye._internal.template.feature import InternalFeature
from officialeye._internal.template.keypoint import InternalKeypoint
from officialeye._internal.template.template_data import TemplateData, TemplateDataFeature, TemplateDataKeypoint


if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.match import Matcher
    # noinspection PyProtectedMember
    from officialeye._api.mutator import Mutator
    # noinspection PyProtectedMember
    from officialeye._api.analysis_result import AnalysisResult


class InternalTemplate(ITemplate):

    def __init__(self, yaml_dict: Dict[str, any], path_to_template: str, /):
        super().__init__()

        self._path_to_template = path_to_template

        self._template_id = yaml_dict["id"]
        self._name = yaml_dict["name"]
        self._source = yaml_dict["source"]

        self._height, self._width, _ = self.load_source_image().shape

        self._source_mutators: List[Mutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["source"]
        ]

        self._target_mutators: List[Mutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["target"]
        ]

        self._keypoints: Dict[str, InternalKeypoint] = {}
        self._features: Dict[str, InternalFeature] = {}

        for keypoint_id in yaml_dict["keypoints"]:
            keypoint_dict = yaml_dict["keypoints"][keypoint_id]
            keypoint_dict["id"] = keypoint_id
            keypoint = InternalKeypoint(self.identifier, keypoint_dict)

            if keypoint.identifier in self._keypoints:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.identifier}'",
                    f"There is already a keypoint with the same identifier '{keypoint.identifier}'."
                )

            if keypoint.identifier in self._features:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.identifier}'",
                    f"There is already a feature with the same identifier '{keypoint.identifier}'."
                )

            self._keypoints[keypoint.identifier] = keypoint

        self._matching = yaml_dict["matching"]
        self._supervision = yaml_dict["supervision"]

        # load feature classes
        self._feature_class_manager = load_template_feature_classes(yaml_dict["feature_classes"], self.identifier)

        # load features
        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = InternalFeature(self.identifier, feature_dict)

            if feature.identifier in self._keypoints:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.identifier}'",
                    f"There is already a keypoint with the same identifier '{feature.identifier}'."
                )

            if feature.identifier in self._features:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.identifier}'",
                    f"There is already a feature with the same identifier '{feature.identifier}'."
                )

            self._features[feature.identifier] = feature

        get_internal_context().add_template(self)

    def load(self):
        raise ErrOperationNotSupported(
            "when calling the load() method of an InternalTemplate instance.",
            "This method can only be called on a Template instance."
        )

    def analyze_async(self, /, *, target: IImage, interpretation_target: IImage | None = None) -> Future:
        raise ErrOperationNotSupported(
            "when calling the analyze_async() method of an InternalTemplate instance.",
            "This method can only be called on a Template instance."
        )

    def analyze(self, /, **kwargs) -> AnalysisResult:
        raise ErrOperationNotSupported(
            "when calling the analyze() method of an InternalTemplate instance.",
            "This method can only be called on a Template instance."
        )

    def _get_source_image_path(self) -> str:
        if os.path.isabs(self._source):
            return self._source
        path_to_template_dir = os.path.dirname(self._path_to_template)
        path = os.path.join(path_to_template_dir, self._source)
        return os.path.normpath(path)

    def get_image(self) -> IImage:
        return InternalImage(path=self._get_source_image_path())

    def get_mutated_image(self) -> IImage:
        img = self.get_image()
        img.apply_mutators(*self._source_mutators)
        return img

    @property
    def identifier(self) -> str:
        return self._template_id

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
    def keypoints(self) -> Iterable[InternalKeypoint]:
        for keypoint_id in self._keypoints:
            yield self._keypoints[keypoint_id]

    @property
    def features(self) -> Iterable[InternalFeature]:
        for feature_id in self._features:
            yield self._features[feature_id]

    def validate(self):
        for feature in self.features:
            feature.validate_feature_class()

    def get_template_data(self) -> TemplateData:
        return TemplateData(
            identifier=self.identifier,
            name=self.name,
            source=self._get_source_image_path(),
            width=self.width,
            height=self.height,
            features=[
                TemplateDataFeature(
                    identifier=f.identifier,
                    x=f.x,
                    y=f.y,
                    w=f.w,
                    h=f.h
                ) for f in self.features
            ],
            keypoints=[
                TemplateDataKeypoint(
                    identifier=k.identifier,
                    x=k.x,
                    y=k.y,
                    w=k.w,
                    h=k.h,
                    matches_min=k.matches_min,
                    matches_max=k.matches_max
                ) for k in self.keypoints
            ],
            source_mutators=self._source_mutators,
            target_mutators=self._target_mutators
        )

    def get_matcher(self, /, *, setup: bool) -> Matcher:
        matcher_id = self._matching["engine"]
        matcher_config = self._matching["config"]

        _matcher = get_internal_context().get_matcher(matcher_id, matcher_config)

        if setup:
            _matcher.setup(self)

        return _matcher

    def get_supervision_engine(self) -> str:
        return self._supervision["engine"]

    def get_supervision_result_choice_engine(self) -> str:
        return self._supervision["result"]

    def get_supervision_config(self) -> dict:
        return self._supervision["config"]

    def get_feature_classes(self) -> FeatureClassManager:
        return self._feature_class_manager

    def get_feature(self, feature_id: str, /) -> InternalFeature:
        assert feature_id in self._features, "Invalid feature id"
        return self._features[feature_id]

    def get_keypoint(self, keypoint_id: str, /) -> InternalKeypoint:
        assert keypoint_id in self._keypoints, "Invalid keypoint id"
        return self._keypoints[keypoint_id]

    def load_source_image(self) -> np.ndarray:

        # TODO: remove this method and migrate to corresponding method of IImage

        _image_path = self._get_source_image_path()

        if not os.path.isfile(_image_path):
            raise ErrIOInvalidPath(
                f"while loading template source image of template '{self.identifier}'.",
                f"Inferred path '{_image_path}' does not refer to a file."
            )

        if not os.access(_image_path, os.R_OK):
            raise ErrIOInvalidPath(
                f"while loading template source image of template '{self.identifier}'.",
                f"The file at path '{_image_path}' could not be read."
            )

        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def get_path(self) -> str:
        return self._path_to_template

    def _load_supervisor(self, kmr: MatchingResult):

        # TODO: abstract this out like we did with the matcher

        superivision_engine = self.get_supervision_engine()

        if superivision_engine == LeastSquaresRegressionSupervisor.ENGINE_ID:
            return LeastSquaresRegressionSupervisor(self.identifier, kmr)

        if superivision_engine == OrthogonalRegressionSupervisor.ENGINE_ID:
            return OrthogonalRegressionSupervisor(self.identifier, kmr)

        if superivision_engine == CombinatorialSupervisor.ENGINE_ID:
            return CombinatorialSupervisor(self.identifier, kmr)

        raise ErrTemplateInvalidSupervisionEngine(
            "while loading supervisor",
            f"unknown supervision engine '{superivision_engine}'"
        )

    def run_analysis(self, target: np.ndarray, /) -> SupervisionResult:
        # find all patterns in the target image

        _timer = Timer()

        with _timer:
            # apply mutators to the target image
            for mutator in self._target_mutators:
                get_internal_afi().info(Verbosity.DEBUG_VERBOSE, f"Applying mutator '{mutator.mutator_id}' to input image.")
                target = mutator.mutate(target)

            # start matching
            matcher = self.get_matcher(setup=True)

            for keypoint in self.keypoints:
                get_internal_afi().info(Verbosity.DEBUG, f"Running matcher for keypoint '{keypoint.identifier}'.")
                assert isinstance(keypoint, InternalKeypoint)
                matcher.match(keypoint)

            keypoint_matching_result = MatchingResult(self.identifier)

            for keypoint in self.keypoints:
                for match in matcher.get_matches_for_keypoint(keypoint):
                    keypoint_matching_result.add_match()
                    # TODO
                    pass

            keypoint_matching_result = matcher.match_finish()

            if get_internal_context().visualization_generation_enabled():
                keypoint_matching_result.debug_print()

            keypoint_matching_result.validate()
            assert keypoint_matching_result.get_total_match_count() > 0

        get_internal_afi().info(
            Verbosity.INFO,
            f"Matching succeeded in {_timer.get_real_time():.2f} seconds of real time "
            f"and {_timer.get_cpu_time():.2f} seconds of CPU time."
        )

        with _timer:
            # run supervision to obtain correspondence between template and target regions
            supervisor = self._load_supervisor(keypoint_matching_result)
            supervision_result = supervisor.run()

            # TODO: rewrite the visualization generation communication logic
            if get_internal_context().visualization_generation_enabled():
                supervision_result_visualizer = SupervisionResultVisualizer(supervision_result, target)
                visualization = supervision_result_visualizer.render()
                get_internal_context().export_image(visualization, file_name="matches.png")

        get_internal_afi().info(
            Verbosity.INFO,
            f"Supervision succeeded in {_timer.get_real_time():.2f} seconds of real time "
            f"and {_timer.get_cpu_time():.2f} seconds of CPU time."
        )

        return supervision_result

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._keypoints)} keypoints, {len(self._features)} features)"
