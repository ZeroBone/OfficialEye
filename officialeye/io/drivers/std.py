from typing import Union

# noinspection PyPackageRequirements
import cv2
import numpy as np

from officialeye.context.singleton import oe_context
from officialeye.io.driver import IODriver
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template
from officialeye.utils.cli_utils import export_and_show_image
from officialeye.utils.logger import print_error


class StandardIODriver(IODriver):

    DRIVER_ID = "std"

    def __init__(self):
        super().__init__(StandardIODriver.DRIVER_ID)

    def output_analyze_result(self, target: cv2.Mat, result: Union[SupervisionResult, None], /):

        if result is None:
            print_error("while running supervisor", f"could not establish correspondence of the image with the template")
            exit(7)

        template = oe_context().get_template(result.template_id)

        application_image = template.load_source_image()

        # extract the features from the target image
        for feature in template.features():
            feature_tl = feature.get_top_left_vec()
            feature_tr = feature.get_top_right_vec()
            feature_bl = feature.get_bottom_left_vec()
            feature_br = feature.get_bottom_right_vec()

            target_tl = result.template_point_to_target_point(feature_tl)
            target_tr = result.template_point_to_target_point(feature_tr)
            target_bl = result.template_point_to_target_point(feature_bl)
            target_br = result.template_point_to_target_point(feature_br)

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
        for feature in template.features():
            application_image = feature.visualize(application_image)

        export_and_show_image(application_image)

    def output_show_result(self, template: Template, img: cv2.Mat):
        export_and_show_image(img, file_name=f"{template.template_id}.png")
