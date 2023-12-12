import os
from typing import Dict

import click
# noinspection PyPackageRequirements
import cv2
import numpy as np

from officialeye.context.singleton import oe_context
from officialeye.debug import DebugInformationContainer
from officialeye.election.election import Election
from officialeye.match.flann_matcher import FlannKeypointMatcher
from officialeye.utils.cli_utils import export_and_show_image
from officialeye.region.feature import TemplateFeature
from officialeye.region.keypoint import TemplateKeypoint


class Template:
    def __init__(self, yaml_dict: dict, path_to_template: str, /):
        self._path_to_template = path_to_template
        self.template_id = str(yaml_dict["id"])

        self.name = str(yaml_dict["name"])
        self._source = str(yaml_dict["source"])

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

        for feature_id in yaml_dict["features"]:
            feature_dict = yaml_dict["features"][feature_id]
            feature_dict["id"] = feature_id
            feature = TemplateFeature(feature_dict, self)
            assert feature.region_id not in self._keypoints, "Duplicate region id of feature"
            assert feature.region_id not in self._features, "Duplicate region id of feature"
            self._features[feature.region_id] = feature

        oe_context().on_template_loaded(self)

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
        path_to_template_dir = os.path.dirname(self._path_to_template)
        path = os.path.join(path_to_template_dir, self._source)
        return os.path.normpath(path)

    def load_source_image(self):
        return cv2.imread(self._get_source_image_path(), cv2.IMREAD_COLOR)

    def _show(self, img):
        for feature in self.features():
            img = feature.draw(img)
        for keypoint in self.keypoints():
            img = keypoint.draw(img)
        return img

    def show(self):
        img = self.load_source_image()
        img = self._show(img)
        export_and_show_image(img)

    def _generate_keypoint_visualization(self):
        kp_vis = np.full((self.height, self.width), 0xff, dtype=np.uint8)

        for kp in self.keypoints():
            kp_img = kp.to_image()
            kp_vis[kp.y:kp.y+kp.h, kp.x:kp.x+kp.w] = kp_img

        return kp_vis

    def generate_keypoint_visualization(self, /):
        mp = self._generate_keypoint_visualization()
        mp = cv2.Mat(mp)
        export_and_show_image(mp)

    def apply(self, target, /, *, debug_mode: bool = False):
        # find all patterns in the target image
        # img = target.copy()

        with click.progressbar(length=len(self._keypoints) + 2, label="Matching") as bar:

            matcher = FlannKeypointMatcher(self.template_id, target,
                                           debug=DebugInformationContainer() if debug_mode else None)

            bar.update(1)

            for i, kp in enumerate(self.keypoints()):
                matcher.match_keypoint(kp)
                bar.update(2 + i)

            keypoint_matching_result = matcher.match_finish()

        if debug_mode:
            matcher.debug_export()
            keypoint_matching_result.debug_print()

        # run election to obtain correspondence between template and target regions

        election = Election(keypoint_matching_result)
        election.run()

        # output_path = "debug.png"
        # cv2.imwrite(output_path, img)
        # click.secho(f"Pattern-match success. Exported '{output_path}'.", bg="green", bold=True)

        # homography = cv2.getPerspectiveTransform(np.float32(source_points), np.float32(destination_points))
        # target_transformed = cv2.warpPerspective(target, np.float32(homography), (self.width, self.height),
        # flags=cv2.INTER_LINEAR)
        # target_transformed = self._show(target_transformed)

        # output_path = "transformed.png"
        # cv2.imwrite(output_path, target_transformed)
        # click.secho(f"Success. Exported '{output_path}'.", bg="green", bold=True)

    def __str__(self):
        return f"{self.name} ({self._source}, {len(self._features)} features)"
