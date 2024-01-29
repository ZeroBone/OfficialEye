import os
from typing import Dict, Generator, List, Union

import cv2

# noinspection PyProtectedMember
from officialeye._api.feedback.verbosity import Verbosity
from officialeye._internal.context.singleton import get_internal_context, get_internal_afi
from officialeye._internal.template.utils import load_mutator_from_dict
from officialeye._internal.timer import Timer
from officialeye.error.errors.io import ErrIOInvalidPath
from officialeye.error.errors.template import (
    ErrTemplateInvalidFeature,
    ErrTemplateInvalidKeypoint,
    ErrTemplateInvalidMatchingEngine,
    ErrTemplateInvalidSupervisionEngine,
)

from officialeye._internal.matching.matcher import Matcher
from officialeye._internal.matching.matchers.sift_flann import SiftFlannMatcher
from officialeye._internal.matching.result import MatchingResult
# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.supervision.supervisors.combinatorial import CombinatorialSupervisor
from officialeye._internal.supervision.supervisors.least_squares_regression import LeastSquaresRegressionSupervisor
from officialeye._internal.supervision.supervisors.orthogonal_regression import OrthogonalRegressionSupervisor
from officialeye._internal.supervision.visualizer import SupervisionResultVisualizer
from officialeye._internal.template.feature_class.loader import load_template_feature_classes
from officialeye._internal.template.feature_class.manager import FeatureClassManager
from officialeye._internal.template.region.feature import TemplateFeature
from officialeye._internal.template.region.keypoint import TemplateKeypoint
# noinspection PyProtectedMember
from officialeye._api.template.region import Feature, Keypoint
from officialeye._internal.template.template_data import TemplateData


class Template:

    def __init__(self, yaml_dict: Dict[str, any], path_to_template: str, /):

        self._path_to_template = path_to_template

        self.template_id = yaml_dict["id"]
        self.name = yaml_dict["name"]
        self._source = yaml_dict["source"]

        self.height, self.width, _ = self.load_source_image().shape

        self._source_mutators: List[Mutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["source"]
        ]

        self._target_mutators: List[Mutator] = [
            load_mutator_from_dict(mutator_dict) for mutator_dict in yaml_dict["mutators"]["target"]
        ]

        self._keypoints: Dict[str, TemplateKeypoint] = {}
        self._features: Dict[str, TemplateFeature] = {}

        for keypoint_id in yaml_dict["keypoints"]:
            keypoint_dict = yaml_dict["keypoints"][keypoint_id]
            keypoint_dict["id"] = keypoint_id
            keypoint = TemplateKeypoint(self.template_id, keypoint_dict)

            if keypoint.region_id in self._keypoints:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.template_id}'",
                    f"There is already a keypoint with the same identifier '{keypoint.region_id}'."
                )

            if keypoint.region_id in self._features:
                raise ErrTemplateInvalidKeypoint(
                    f"while initializing keypoint '{keypoint_id}' of template '{self.template_id}'",
                    f"There is already a feature with the same identifier '{keypoint.region_id}'."
                )

            self._keypoints[keypoint.region_id] = keypoint

        self._matching = yaml_dict["matching"]
        self._supervision = yaml_dict["supervision"]

        # load feature classes
        self._feature_class_manager = load_template_feature_classes(yaml_dict["feature_classes"], self.template_id)

        # load features
        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = TemplateFeature(self.template_id, feature_dict)

            if feature.region_id in self._keypoints:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.template_id}'",
                    f"There is already a keypoint with the same identifier '{feature.region_id}'."
                )

            if feature.region_id in self._features:
                raise ErrTemplateInvalidFeature(
                    f"while initializing feature '{feature_id}' of template '{self.template_id}'",
                    f"There is already a feature with the same identifier '{feature.region_id}'."
                )

            self._features[feature.region_id] = feature

        get_internal_context().add_template(self)

    def validate(self):
        for feature in self.features():
            feature.validate_feature_class()

    def get_template_data(self) -> TemplateData:

        data = TemplateData(
            identifier=self.template_id,
            name=self.name,
            source=self._get_source_image_path(),
            width=self.width,
            height=self.height,
            features=[
                Feature(identifier=f.region_id, x=f.x, y=f.y, w=f.w, h=f.h) for f in self.features()
            ],
            keypoints=[
                Keypoint(
                    identifier=k.region_id,
                    x=k.x,
                    y=k.y,
                    w=k.w,
                    h=k.h,
                    matches_min=k.get_matches_min(),
                    matches_max=k.get_matches_max()
                ) for k in self.keypoints()
            ],
            source_mutators=self._source_mutators,
            target_mutators=self._target_mutators
        )

        return data

    def get_matching_engine(self) -> str:
        return self._matching["engine"]

    def get_supervision_engine(self) -> str:
        return self._supervision["engine"]

    def get_supervision_result(self) -> str:
        return self._supervision["result"]

    def get_supervision_config(self) -> dict:
        return self._supervision["config"]

    def get_matching_config(self) -> dict:
        matching_config = self._matching["config"]
        assert isinstance(matching_config, dict)
        return matching_config

    def get_feature_classes(self) -> FeatureClassManager:
        return self._feature_class_manager

    def _load_keypoint_matcher(self, target_img: cv2.Mat, /) -> Matcher:

        matching_engine = self.get_matching_engine()

        if matching_engine == SiftFlannMatcher.ENGINE_ID:
            return SiftFlannMatcher(self.template_id, target_img)

        raise ErrTemplateInvalidMatchingEngine(
            "while loading keypoint matcher",
            f"unknown matching engine '{matching_engine}'"
        )

    def features(self) -> Generator[TemplateFeature, None, None]:
        for feature_id in self._features:
            yield self._features[feature_id]

    def get_feature(self, feature_id: str, /) -> TemplateFeature:
        assert feature_id in self._features, "Invalid feature id"
        return self._features[feature_id]

    def keypoints(self) -> Generator[TemplateKeypoint, None, None]:
        for keypoint_id in self._keypoints:
            yield self._keypoints[keypoint_id]

    def get_keypoint(self, keypoint_id: str, /) -> TemplateKeypoint:
        assert keypoint_id in self._keypoints, "Invalid keypoint id"
        return self._keypoints[keypoint_id]

    def _get_source_image_path(self) -> str:
        if os.path.isabs(self._source):
            return self._source
        path_to_template_dir = os.path.dirname(self._path_to_template)
        path = os.path.join(path_to_template_dir, self._source)
        return os.path.normpath(path)

    def load_source_image(self) -> cv2.Mat:

        _image_path = self._get_source_image_path()

        if not os.path.isfile(_image_path):
            raise ErrIOInvalidPath(
                f"while loading template source image of template '{self.template_id}'.",
                f"Inferred path '{_image_path}' does not refer to a file."
            )

        if not os.access(_image_path, os.R_OK):
            raise ErrIOInvalidPath(
                f"while loading template source image of template '{self.template_id}'.",
                f"The file at path '{_image_path}' could not be read."
            )

        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def _load_supervisor(self, kmr: MatchingResult):
        superivision_engine = self.get_supervision_engine()

        if superivision_engine == LeastSquaresRegressionSupervisor.ENGINE_ID:
            return LeastSquaresRegressionSupervisor(self.template_id, kmr)

        if superivision_engine == OrthogonalRegressionSupervisor.ENGINE_ID:
            return OrthogonalRegressionSupervisor(self.template_id, kmr)

        if superivision_engine == CombinatorialSupervisor.ENGINE_ID:
            return CombinatorialSupervisor(self.template_id, kmr)

        raise ErrTemplateInvalidSupervisionEngine(
            "while loading supervisor",
            f"unknown supervision engine '{superivision_engine}'"
        )

    def run_analysis(self, target: cv2.Mat, /) -> Union[SupervisionResult, None]:
        # find all patterns in the target image

        _timer = Timer()

        with _timer:
            # apply mutators to the target image
            for mutator in self._target_mutators:
                get_internal_afi().info(Verbosity.DEBUG_VERBOSE, f"Applying mutator '{mutator.mutator_id}' to input image.")
                target = mutator.mutate(target)

            # start matching
            matcher = self._load_keypoint_matcher(target)

            for keypoint in self.keypoints():
                keypoint_pattern = keypoint.to_image()
                get_internal_afi().info(Verbosity.DEBUG, f"Running matcher for keypoint '{keypoint.region_id}'.")
                matcher.match_keypoint(keypoint_pattern, keypoint.region_id)

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

            if supervision_result is None:
                return None

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
