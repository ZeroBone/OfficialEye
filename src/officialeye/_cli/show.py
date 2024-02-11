import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.template import Template
from officialeye._cli.context import CLIContext
from officialeye._cli.utils import visualize_feature, visualize_keypoint

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity


def _visualize_regions(template: Template, background_img: np.ndarray, /, *,
                       hide_features: bool = False, hide_keypoints: bool = False) -> np.ndarray:

    img = background_img

    if not hide_features:
        for feature in template.features:
            img = visualize_feature(feature, img)

    if not hide_keypoints:
        for keypoint in template.keypoints:
            img = visualize_keypoint(keypoint, img)

    return img


def do_show(context: CLIContext, /, *, template_path: str, **kwargs):

    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    template = Template(context.get_api_context(), path=template_path)

    template_img = template.get_image().load()

    template_img_mutated = template.get_mutated_image().load()

    if template_img_mutated.shape == template_img.shape:
        background_img = template_img_mutated
    else:

        context.get_terminal_ui().warn(
            Verbosity.INFO_VERBOSE,
            f"One of the source mutators of the '{template.identifier}' template has changed the shape of the image. "
            f"To ensure that the regions of the template are visualized correctly, "
            f"the original template image had to be used as the background."
        )

        background_img = template_img

    visualization = _visualize_regions(template, background_img, **kwargs)

    context.export_and_show_image(visualization, file_name=f"{template.identifier}.png")
