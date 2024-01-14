# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error import OEError
from officialeye.error.printing import oe_error_print_error
from officialeye.io.driver import IODriver
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template
from officialeye.util.cli_utils import export_and_show_image, export_image


class TestIODriver(IODriver):

    DRIVER_ID = "test"

    def __init__(self):
        super().__init__()

        self.visualize_features: bool = True

    def output_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = oe_context().get_template(result.template_id)

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

        if oe_context().quiet_mode:
            export_image(application_image, file_name="supervision_result.png")
        else:
            export_and_show_image(application_image, file_name="supervision_result.png")

    def output_show_result(self, template: Template, img: cv2.Mat, /):
        if oe_context().quiet_mode:
            export_image(img, file_name=f"{template.template_id}.png")
        else:
            export_and_show_image(img, file_name=f"{template.template_id}.png")

    def output_error(self, error: OEError, /):
        oe_error_print_error(error)
