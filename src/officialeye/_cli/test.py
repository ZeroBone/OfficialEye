from typing import List

import numpy as np
from rich.panel import Panel

# noinspection PyProtectedMember
from officialeye._api.detection import detect

# noinspection PyProtectedMember
from officialeye._api.image import Image

# noinspection PyProtectedMember
from officialeye._api.template.template import Template

# noinspection PyProtectedMember
from officialeye._api.template.template_interface import ITemplate
from officialeye._cli.context import CLIContext
from officialeye._cli.utils import visualize_feature

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
            target_path: str, template_paths: List[str], show_features: bool):
    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    api_context = context.get_api_context()

    target_image = Image(api_context, path=target_path)

    templates = [Template(api_context, path=template_path) for template_path in template_paths]

    result = detect(api_context, *templates, target=target_image)

    context.get_terminal_ui().echo(
        Verbosity.INFO,
        Panel(
            f"Detected template '{result.template.identifier}' ({result.template.name}).",
            expand=False,
            title="Result",
            border_style="turquoise2"
        )
    )

    visualization = _get_background(context, result.template)
    target_image_mat = target_image.load()

    for feature in result.template.features:
        feature_image_mat = result.warp_feature(feature, target_image_mat)

        assert feature_image_mat.shape == (feature.h, feature.w, 3)

        feature_image_mutated_mat = feature.apply_mutators_to_image(feature_image_mat)

        if feature_image_mat.shape == feature_image_mutated_mat.shape:
            # mutators didn't change the shape of the image
            feature.insert_into_image(visualization, feature_image_mutated_mat)
        else:
            # some mutator has altered the shape of the feature image.
            # this means that we can no longer safely insert the mutated feature into the visualization.
            # therefore, we have to fall back to inserting the feature image unmutated
            context.get_terminal_ui().warn(
                Verbosity.INFO,
                f"Could not visualize the '{feature.identifier}' feature of the '{feature.template.identifier}' template, "
                f"because one of the mutators (corresponding to this feature) did not preserve the shape of the image. "
                f"Falling back to the non-mutated version of the feature image."
            )

            feature.insert_into_image(visualization, feature_image_mat)

    if show_features:
        # visualize features on the image
        for feature in result.template.features:
            visualization = visualize_feature(feature, visualization)

    context.export_and_show_image(visualization, file_name=f"{result.template.identifier}.png")
