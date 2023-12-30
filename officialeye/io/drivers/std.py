# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error.error import OEError
from officialeye.error.printing import oe_error_print_error
from officialeye.io.driver import IODriver
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template
from officialeye.util.cli_utils import export_and_show_image


class StandardIODriver(IODriver):

    DRIVER_ID = "std"

    def __init__(self):
        super().__init__(StandardIODriver.DRIVER_ID)

    def output_analyze_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = oe_context().get_template(result.template_id)

        application_image = template.load_source_image()

        # extract the features from the target image
        for feature in template.features():
            feature_img = result.get_feature_warped_region(target, feature)
            feature.insert_into_image(application_image, feature_img)

        # visualize features on the image
        for feature in template.features():
            application_image = feature.visualize(application_image)

        export_and_show_image(application_image)

    def output_show_result(self, template: Template, img: cv2.Mat, /):
        export_and_show_image(img, file_name=f"{template.template_id}.png")

    def output_error(self, error: OEError, /):
        oe_error_print_error(error)
