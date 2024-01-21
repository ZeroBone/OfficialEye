import json
import sys

import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.error import OEError
from officialeye._internal.error.errors.io import ErrIOOperationNotSupportedByDriver
from officialeye._internal.io.driver import IODriver
from officialeye._internal.supervision.result import SupervisionResult
from officialeye._internal.template.template import Template


def _output_dict(d: dict):
    json.dump(d, sys.stdout, indent=4, ensure_ascii=False)
    sys.stdout.write("\n")
    sys.stdout.flush()


class RunIODriver(IODriver):

    def __init__(self, context: Context, /):
        super().__init__(context)

    def handle_show_result(self, template: Template, img: cv2.Mat, /):
        raise ErrIOOperationNotSupportedByDriver(
            f"while trying to output the result of showing the template '{template.template_id}'",
            f"Driver 'run' does not support this operation."
        )

    def handle_error(self, error: OEError, /):
        _output_dict({
            "ok": False,
            "err": error.serialize()
        })

    def handle_supervision_result(self, target: cv2.Mat, result: SupervisionResult, /):

        assert result is not None

        template = self._context.get_template(result.template_id)

        interpretation_dict = {}

        # extract the features from the target image
        for feature in template.features():

            feature_class = feature.get_feature_class()

            if feature_class is None:
                continue

            feature_img = result.get_feature_warped_region(target, feature)
            feature_img_mutated = feature.apply_mutators_to_image(feature_img)
            interpretation = feature.interpret_image(feature_img_mutated)

            interpretation_dict[feature.region_id] = interpretation

        _output_dict({
            "ok": True,
            "template": result.template_id,
            "score": result.get_score(),
            "features": interpretation_dict
        })
