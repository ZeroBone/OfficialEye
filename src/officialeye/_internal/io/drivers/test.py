import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.error import OEError
from officialeye._internal.io.driver import IODriver
from officialeye._internal.logger.singleton import get_logger
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.template.template import Template


class TestIODriver(IODriver):

    def __init__(self, context: Context, /):
        super().__init__(context)

        self.visualize_features: bool = True

    def handle_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = self._context.get_template(result.template_id)

        application_image = template.load_source_image()

        # extract the features from the target image
        for feature in template.features():
            feature_img = result.get_feature_warped_region(target, feature)

            feature_img_mutated = feature.apply_mutators_to_image(feature_img)

            if feature_img.shape == feature_img_mutated.shape:
                # mutators didn't change the shape of the image
                feature.insert_into_image(application_image, feature_img_mutated)
            else:
                # some mutator has altered the shape of the feature image.
                # this means that we can no longer safely insert the mutated feature into the visualization.
                # therefore, we have to fall back to inserting the feature image unmutated
                get_logger().warn(f"Could not visualize the '{feature.region_id}' feature of the '{feature.get_template().template_id}' template, "
                                  f"because one of the mutators (corresponding to this feature) did not preserve the shape of the image. "
                                  f"Falling back to the non-mutated version of the feature image.")
                feature.insert_into_image(application_image, feature_img)

        if self.visualize_features:
            # visualize features on the image
            for feature in template.features():
                application_image = feature.visualize(application_image)

        self._context.export_primary_image(application_image, file_name="supervision_result.png")

    def handle_show_result(self, template: Template, img: cv2.Mat, /):
        self._context.export_primary_image(img, file_name=f"{template.template_id}.png")

    def handle_error(self, error: OEError, /):
        get_logger().error_oe_error(error)
