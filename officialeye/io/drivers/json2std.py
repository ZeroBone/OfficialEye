import json
import sys

# noinspection PyPackageRequirements
import cv2
from pytesseract import pytesseract

from officialeye.context.singleton import oe_context
from officialeye.error.error import OEError
from officialeye.error.errors.io import ErrIOOperationNotSupportedByDriver
from officialeye.io.driver import IODriver
from officialeye.supervision.result import SupervisionResult
from officialeye.template.template import Template


def _output_dict(d: dict):
    json.dump(d, sys.stdout, indent=4, ensure_ascii=False)
    sys.stdout.write("\n")
    sys.stdout.flush()


class Json2StdIODriver(IODriver):

    DRIVER_ID = "json2std"

    def __init__(self):
        super().__init__(Json2StdIODriver.DRIVER_ID)

    def output_show_result(self, template: Template, img: cv2.Mat, /):
        raise ErrIOOperationNotSupportedByDriver(
            f"while trying to output the result of showing the template '{template.template_id}'",
            f"Driver '{Json2StdIODriver.DRIVER_ID}' does not support this operation."
        )

    def output_error(self, error: OEError, /):
        _output_dict({
            "ok": False,
            "err": error.serialize()
        })

    def output_analyze_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = oe_context().get_template(result.template_id)

        features_dict = {}

        # extract the features from the target image
        for feature in template.features():
            if feature.get_type() != "text":
                continue
            feature_img = result.get_feature_warped_region(target, feature)

            data = pytesseract.image_to_string(feature_img, lang="rus", config="--dpi 10000 --oem 3 --psm 6")

            features_dict[feature.region_id] = data.strip()

        _output_dict({
            "ok": True,
            "features": features_dict
        })
