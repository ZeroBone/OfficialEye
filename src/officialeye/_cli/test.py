from typing import List

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate
# noinspection PyProtectedMember
from officialeye._api.detection import detect
# noinspection PyProtectedMember
from officialeye._api.image import Image
# noinspection PyProtectedMember
from officialeye._api.template.template import Template
from officialeye._cli.context import CLIContext
# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity


def _get_background(context: CLIContext, template: ITemplate, /) -> np.ndarray:

    raw_image = template.get_image().load()
    mutated_image = template.get_mutated_image().load()

    if raw_image.shape == mutated_image.shape:
        return mutated_image

    context.get_terminal_ui().warn(
        Verbosity.INFO,
        f"Could not use the mutated version of the '{template.identifier}' template "
        f"because one of the source mutators did not preserve the shape of the image. "
        f"Falling back to the non-mutated version of the source image."
    )

    return raw_image


def do_test(context: CLIContext, /, *,
            target_path: str, template_paths: List[str], visualize: bool, show_features: bool):
    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    api_context = context.get_api_context()

    target_image = Image(api_context, path=target_path)

    templates = [Template(api_context, path=template_path) for template_path in template_paths]

    result = detect(api_context, *templates, target=target_image)

    template_image_mat = _get_background(context, result.template)
    target_image_mat = target_image.load()

    for feature in result.template.features:
        feature_image_mat = result.warp_feature(feature, target_image_mat)

    # TODO: remove this unnecessary message
    context.get_terminal_ui().info(Verbosity.INFO, "Running complete!")
