from typing import List

from officialeye._cli.context import CLIContext


def do_run(context: CLIContext, /, *, target_path: str, template_paths: List[str], interpret_path: str | None, visualize: bool):
    # print OfficialEye logo and other introductory information (if necessary)
    context.print_intro()
