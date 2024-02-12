from __future__ import annotations

from typing import TYPE_CHECKING, List

from rich.console import Group
from rich.json import JSON
from rich.panel import Panel
from rich.table import Table

# noinspection PyProtectedMember
from officialeye._api.detection import detect

# noinspection PyProtectedMember
from officialeye._api.image import Image

# noinspection PyProtectedMember
from officialeye._api.template.template import Template
from officialeye._cli.context import CLIContext

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity

if TYPE_CHECKING:
    from officialeye.types import FeatureInterpretation


def do_run(context: CLIContext, /, *, target_path: str, template_paths: List[str], interpret_path: str | None, visualize: bool):
    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()

    # TODO: implement visualization generation
    # TODO: update the example in the documentation

    api_context = context.get_api_context()

    target_image = Image(api_context, path=target_path)

    interpretation_target_image = target_image if interpret_path is None else Image(api_context, path=interpret_path)

    templates = [Template(api_context, path=template_path) for template_path in template_paths]

    result = detect(api_context, *templates, target=target_image)

    interpretation_result = result.interpret(target=interpretation_target_image)

    table = Table(title="Feature interpretations")

    table.add_column("Feature", justify="right")
    table.add_column("Interpretation", justify="left")

    for feature in interpretation_result.template.features:
        interpretation: FeatureInterpretation = interpretation_result.get_feature_interpretation(feature)

        interpretation_visualization = JSON.from_data(interpretation, indent=4)

        table.add_row(feature.identifier, interpretation_visualization)

    context.get_terminal_ui().echo(
        Verbosity.INFO,
        Panel(
            Group(
                f"Detected template '{result.template.identifier}' ({result.template.name}).",
                table
            ),
            expand=False,
            title="Result",
            border_style="turquoise2"
        )
    )
