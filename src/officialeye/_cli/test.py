from typing import List

# noinspection PyProtectedMember
from officialeye._api.analysis import analyze
# noinspection PyProtectedMember
from officialeye._api.image import Image
# noinspection PyProtectedMember
from officialeye._api.template.template import Template
from officialeye._cli.context import CLIContext
# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity


def do_test(context: CLIContext, /, *, target_path: str, template_paths: List[str], interpret_path: str | None, visualize: bool, show_features: bool):
    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    api_context = context.get_api_context()

    target_img = Image(api_context, path=target_path)

    interpretation_target_image = target_img if interpret_path is None else Image(api_context, path=interpret_path)

    templates = [Template(api_context, path=template_path) for template_path in template_paths]

    result = analyze(api_context, *templates, target=target_img, interpretation_target=interpretation_target_image)

    context.get_terminal_ui().info(Verbosity.INFO, "Running complete!")
