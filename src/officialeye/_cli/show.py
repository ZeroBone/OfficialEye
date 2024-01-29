from typing import Tuple

import cv2

from officialeye import Template, Region
from officialeye.feedback import Verbosity
from officialeye._cli.context import CLIContext


_LABEL_COLOR_DEFAULT = (0, 0, 0xff)
_VISUALIZATION_SCALE_COEFF = 1.0 / 1400.0

_FEATURE_RECT_COLOR = (0, 0xff, 0)
_KEYPOINT_RECT_COLOR = (0, 0, 0xff)


def _visualize_region(region: Region, img: cv2.Mat, /, *, rect_color: Tuple[int, int, int], label_color=_LABEL_COLOR_DEFAULT) -> cv2.Mat:

    img = cv2.rectangle(img, (region.x, region.y), (region.x + region.w, region.y + region.h), rect_color, 4)

    label_origin = (
        region.x + int(10 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
        region.y + int(30 * img.shape[0] * _VISUALIZATION_SCALE_COEFF)
    )

    font_scale = img.shape[0] * _VISUALIZATION_SCALE_COEFF
    img = cv2.putText(
        img,
        region.identifier,
        label_origin,
        cv2.FONT_HERSHEY_SIMPLEX,
        font_scale,
        label_color,
        int(2 * img.shape[0] * _VISUALIZATION_SCALE_COEFF),
        cv2.LINE_AA
    )

    return img


def _visualize_regions(template: Template, background_img: cv2.Mat, /, *,
                       hide_features: bool = False, hide_keypoints: bool = False) -> cv2.Mat:

    img = background_img

    if not hide_features:
        for feature in template.features:
            img = _visualize_region(feature, img, rect_color=_FEATURE_RECT_COLOR)

    if not hide_keypoints:
        for keypoint in template.keypoints:
            img = _visualize_region(keypoint, img, rect_color=_KEYPOINT_RECT_COLOR)

    return img


def do_show(context: CLIContext, /, *, template_path: str, **kwargs):

    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    template = Template(context.get_api_context(), path=template_path)

    template_img = template.get_image()

    template_img_mutated = template.get_mutated_image()

    if template_img_mutated.shape == template_img.shape:
        background_img = template_img_mutated
    else:

        context.get_terminal_ui().warn(
            Verbosity.INFO,
            f"One of the source mutators of the '{template.identifier}' template has changed the shape of the image. "
            f"To ensure that the regions of the template are visualized correctly, "
            f"the original template image had to be used as the background."
        )

        background_img = template_img

    visualization = _visualize_regions(template, background_img, **kwargs)

    context.export_and_show_image(visualization, file_name=f"{template.identifier}.png")
