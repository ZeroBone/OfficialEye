import os
from typing import Dict

# noinspection PyPackageRequirements
import cv2
import numpy as np

from officialeye.context.singleton import oe_context
from officialeye.match.matcher import KeypointMatcher
from officialeye.match.matchers.sift_flann import SiftFlannKeypointMatcher
from officialeye.match.result import KeypointMatchingResult
from officialeye.region.feature import TemplateFeature
from officialeye.region.keypoint import TemplateKeypoint
from officialeye.supervision.supervisors.combinatorial import CombinatorialSupervisor
from officialeye.supervision.supervisors.least_squares_regression import LeastSquaresRegressionSupervisor
from officialeye.supervision.supervisors.orthogonal_regression import OrthogonalRegressionSupervisor
from officialeye.supervision.visualizer import SupervisionResultVisualizer
from officialeye.utils.cli_utils import export_and_show_image, print_error


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
            assert keypoint.region_id not in self._keypoints, "Duplicate region id of keypoint"
            assert keypoint.region_id not in self._features, "Duplicate region id of keypoint"
            self._keypoints[keypoint.region_id] = keypoint

        self._matching = yaml_dict["matching"]
        self._supervision = yaml_dict["supervision"]

        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = TemplateFeature(feature_dict, self)
            assert feature.region_id not in self._keypoints, "Duplicate region id of feature"
            assert feature.region_id not in self._features, "Duplicate region id of feature"
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

    def load_keypoint_matcher(self, target_img: cv2.Mat, /) -> KeypointMatcher:
        matching_engine = self.get_matching_engine()

        if matching_engine == SiftFlannKeypointMatcher.ENGINE_ID:
            return SiftFlannKeypointMatcher(self.template_id, target_img)

        print_error("while loading keypoint matcher", f"unknown matching engine '{matching_engine}'")
        exit(5)

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
        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def _show(self, img: cv2.Mat) -> cv2.Mat:
        for feature in self.features():
            img = feature.visualize(img)
        for keypoint in self.keypoints():
            img = keypoint.visualize(img)
        return img

    def show(self):
        img = self.load_source_image()
        img = self._show(img)
        export_and_show_image(img)

    def _load_supervisor(self, kmr: KeypointMatchingResult):
        superivision_engine = self.get_supervision_engine()

        if superivision_engine == LeastSquaresRegressionSupervisor.ENGINE_ID:
            return LeastSquaresRegressionSupervisor(self.template_id, kmr)

        if superivision_engine == OrthogonalRegressionSupervisor.ENGINE_ID:
            return OrthogonalRegressionSupervisor(self.template_id, kmr)

        if superivision_engine == CombinatorialSupervisor.ENGINE_ID:
            return CombinatorialSupervisor(self.template_id, kmr)

        print_error("while loading supervisor", f"unknown supervision engine '{superivision_engine}'")
        exit(6)

    def analyze(self, target, /):
        # find all patterns in the target image

        matcher = self.load_keypoint_matcher(target)

        for i, kp in enumerate(self.keypoints()):
            matcher.match_keypoint(kp)

        keypoint_matching_result = matcher.match_finish()

        if oe_context().debug_mode:
            matcher.debug().export()
            keypoint_matching_result.debug_print()

        # run supervision to obtain correspondence between template and target regions
        supervisor = self._load_supervisor(keypoint_matching_result)
        supervision = supervisor.run()

        if supervision is None:
            print_error("while running supervisor", f"could not establish correspondence of the image with the template")
            exit(7)

        if oe_context().debug_mode:
            supervision_result_visualizer = SupervisionResultVisualizer(supervision, target)
            visualization = supervision_result_visualizer.render()
            supervisor.debug().add_image(visualization)
            supervisor.debug().export()

        application_image = self.load_source_image()

        # extract the features from the target image
        for feature in self.features():
            feature_tl = feature.get_top_left_vec()
            feature_tr = feature.get_top_right_vec()
            feature_bl = feature.get_bottom_left_vec()
            feature_br = feature.get_bottom_right_vec()

            target_tl = supervision.template_point_to_target_point(feature_tl)
            target_tr = supervision.template_point_to_target_point(feature_tr)
            target_bl = supervision.template_point_to_target_point(feature_bl)
            target_br = supervision.template_point_to_target_point(feature_br)

            dest_tl = np.array([0, 0], dtype=np.float64)
            dest_tr = np.array([feature.w, 0], dtype=np.float64)
            dest_br = np.array([feature.w, feature.h], dtype=np.float64)
            dest_bl = np.array([0, feature.h], dtype=np.float64)

            source_points = [target_tl, target_tr, target_br, target_bl]
            destination_points = [dest_tl, dest_tr, dest_br, dest_bl]

            homography = cv2.getPerspectiveTransform(np.float32(source_points), np.float32(destination_points))
            target_transformed = cv2.warpPerspective(
                target,
                np.float32(homography),
                (feature.w, feature.h),
                flags=cv2.INTER_LINEAR
            )

            # export_and_show_image(target_transformed)
            feature.insert_into_image(application_image, target_transformed)

        # visualize features on the image
        for feature in self.features():
            application_image = feature.visualize(application_image)

        export_and_show_image(application_image)

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._keypoints)} keypoints, {len(self._features)} features)"
