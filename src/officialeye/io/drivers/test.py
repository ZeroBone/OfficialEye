# noinspection PyPackageRequirements
import cv2

from officialeye.context.context import Context
from officialeye.error.error import OEError
from officialeye.io.driver import IODriver
from officialeye.logger.singleton import get_logger
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template


class TestIODriver(IODriver):

    def __init__(self, context: Context, /):
        super().__init__(context)

        self.visualize_features: bool = True

    def output_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = self._context.get_template(result.template_id)

        application_image = template.load_source_image()

        # extract the features from the target image
        for feature in template.features():
            feature_img = result.get_feature_warped_region(target, feature)
            feature_img_mutated = feature.apply_mutators_to_image(feature_img)
            feature.insert_into_image(application_image, feature_img_mutated)

        if self.visualize_features:
            # visualize features on the image
            for feature in template.features():
                application_image = feature.visualize(application_image)

        self._context.export_primary_image(application_image, file_name="supervision_result.png")

    def output_show_result(self, template: Template, img: cv2.Mat, /):
        self._context.export_primary_image(img, file_name=f"{template.template_id}.png")

    def output_error(self, error: OEError, /):
        get_logger().error_oe_error(error)
