import os
import time
from typing import Dict, Union

# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error.errors.io import ErrIOInvalidPath
from officialeye.error.errors.template import ErrTemplateInvalidSupervisionEngine, ErrTemplateInvalidMatchingEngine, ErrTemplateInvalidKeypoint, \
    ErrTemplateInvalidFeature
from officialeye.match.matcher import KeypointMatcher
from officialeye.match.matchers.sift_flann import SiftFlannKeypointMatcher
from officialeye.match.result import KeypointMatchingResult
from officialeye.region.feature import TemplateFeature
from officialeye.region.keypoint import TemplateKeypoint
from officialeye.supervision.result import SupervisionResult
from officialeye.supervision.supervisors.combinatorial import CombinatorialSupervisor
from officialeye.supervision.supervisors.least_squares_regression import LeastSquaresRegressionSupervisor
from officialeye.supervision.supervisors.orthogonal_regression import OrthogonalRegressionSupervisor
from officialeye.supervision.visualizer import SupervisionResultVisualizer
from officialeye.util.logger import oe_debug, oe_info


class Template:

    def __init__(self, yaml_dict: dict, path_to_template: str, /):
        self._path_to_template = path_to_template
        self.template_id = yaml_dict["id"]
        self.name = yaml_dict["name"]
        self._source = yaml_dict["source"]

        self.height, self.width, _ = self.load_source_image().shape

        self._keypoints: Dict[str, TemplateKeypoint] = {}
        self._features: Dict[str, TemplateFeature] = {}

        for keypoint_id in yaml_dict["keypoints"]:
            keypoint_dict = yaml_dict["keypoints"][keypoint_id]
            keypoint_dict["id"] = keypoint_id
            keypoint = TemplateKeypoint(keypoint_dict, self)

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

        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = TemplateFeature(feature_dict, self)

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

        oe_context().on_template_loaded(self)

    def get_matching_engine(self) -> str:
        return self._matching["engine"]

    def get_supervision_engine(self) -> str:
        return self._supervision["engine"]

    def get_supervision_result(self) -> str:
        return self._supervision["result"]

    def get_supervision_config(self) -> dict:
        return self._supervision["config"]

    def get_matching_config(self) -> dict:
        return self._matching["config"]

    def load_keypoint_matcher(self, target_img: cv2.Mat, /) -> KeypointMatcher:
        matching_engine = self.get_matching_engine()

        if matching_engine == SiftFlannKeypointMatcher.ENGINE_ID:
            return SiftFlannKeypointMatcher(self.template_id, target_img)

        raise ErrTemplateInvalidMatchingEngine(
            "while loading keypoint matcher",
            f"unknown matching engine '{matching_engine}'"
        )

    def features(self):
        for feature_id in self._features:
            yield self._features[feature_id]

    def get_feature(self, feature_id: str, /) -> TemplateFeature:
        assert feature_id in self._features, "Invalid feature id"
        return self._features[feature_id]

    def keypoints(self):
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
                f"Inferred path at '{_image_path}' is not readable."
            )

        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def _show(self, img: cv2.Mat) -> cv2.Mat:
        for feature in self.features():
            img = feature.visualize(img)
        for keypoint in self.keypoints():
            img = keypoint.visualize(img)
        return img

    def show(self) -> cv2.Mat:
        img = self.load_source_image()
        return self._show(img)

    def _load_supervisor(self, kmr: KeypointMatchingResult):
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

    def analyze(self, target: cv2.Mat, /) -> Union[SupervisionResult, None]:
        # find all patterns in the target image

        _analysis_start_time = time.perf_counter(), time.process_time()

        matcher = self.load_keypoint_matcher(target)

        for kp in self.keypoints():
            oe_debug(f"Running matcher for keypoint '{kp.region_id}'.")
            matcher.match_keypoint(kp)

        keypoint_matching_result = matcher.match_finish()

        if oe_context().debug_mode:
            matcher.debug().export()
            keypoint_matching_result.debug_print()

        keypoint_matching_result.validate()

        _matching_ended_time = time.perf_counter(), time.process_time()

        oe_info(f"Matching succeeded in {_matching_ended_time[0] - _analysis_start_time[0]:.2f} seconds of real time "
                f"and {_matching_ended_time[1] - _analysis_start_time[1]:.2f} seconds of CPU time.")

        # run supervision to obtain correspondence between template and target regions
        supervisor = self._load_supervisor(keypoint_matching_result)
        supervision_result = supervisor.run()

        if supervision_result is None:
            return None

        if oe_context().debug_mode:
            supervision_result_visualizer = SupervisionResultVisualizer(supervision_result, target)
            visualization = supervision_result_visualizer.render()
            supervisor.debug().add_image(visualization)
            supervisor.debug().export()

        _supervision_ended_time = time.perf_counter(), time.process_time()

        oe_info(f"Supervision succeeded in {_supervision_ended_time[0] - _matching_ended_time[0]:.2f} seconds of real time "
                f"and {_supervision_ended_time[1] - _matching_ended_time[1]:.2f} seconds of CPU time.")

        return supervision_result

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._keypoints)} keypoints, {len(self._features)} features)"
