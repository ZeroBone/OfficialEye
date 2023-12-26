from typing import List

import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.meta import OFFICIALEYE_GITHUB, OFFICIALEYE_VERSION, print_logo
from officialeye.template.analyze import do_analyze
from officialeye.template.parser import load_template
from officialeye.template.show import do_show
from officialeye.utils.logger import oe_info, oe_warn


@click.group()
@click.option("-d", "--debug", is_flag=True, show_default=True, default=False, help="Enable debug mode.")
@click.option("--dedir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify debug export directory.")
@click.option("--edir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify export directory.")
@click.option("-q", "--quiet", is_flag=True, show_default=True, default=False, help="Disable standard output messages.")
@click.option("-v", "--verbose", is_flag=True, show_default=True, default=False, help="Enable verbose logging.")
@click.option("-dl", "--disable-logo", is_flag=True, show_default=True, default=False, help="Disable the officialeye logo.")
@click.option("--io", type=str, show_default=False, default="std", help="Specify the IO driver.")
def cli(debug: bool, dedir: str, edir: str, quiet: bool, verbose: bool, disable_logo: bool, io: str):

    oe_context().debug_mode = debug
    oe_context().quiet_mode = quiet
    oe_context().verbose_mode = verbose
    oe_context().disable_logo = disable_logo
    oe_context().io_driver_id = io

    if not quiet and not disable_logo:
        print_logo()

    if dedir is not None:
        oe_context().debug_export_directory = dedir

    if edir is not None:
        oe_context().export_directory = edir

    if oe_context().debug_mode:
        oe_warn("Debug mode enabled. Disable for production use to improve performance.")


@click.command()
@click.argument("template_path", type=click.Path(exists=True, file_okay=True, readable=True))
def show(template_path: str):
    """Exports template as an image with features visualized."""
    template = load_template(template_path)
    do_show(template)
    oe_context().dispose()


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
def analyze(target_path: str, template_paths: List[str], workers: int):
    """Applies one or more templates to an image."""

    # load target image
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)

    templates = [load_template(template_path) for template_path in template_paths]

    do_analyze(target, templates, num_workers=workers)

    oe_context().dispose()


@click.command()
def homepage():
    """Go to the officialeye's official GitHub homepage."""
    oe_info(f"Opening {OFFICIALEYE_GITHUB}")
    click.launch(OFFICIALEYE_GITHUB)
    oe_context().dispose()


@click.command()
def version():
    """Print the version of OfficialEye."""
    oe_info(f"Version: v{OFFICIALEYE_VERSION}")
    oe_context().dispose()


cli.add_command(show)
cli.add_command(analyze)
cli.add_command(homepage)
cli.add_command(version)

if __name__ == "__main__":
    cli()
