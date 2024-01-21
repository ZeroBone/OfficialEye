"""
OfficialEye main entry point.
"""

from typing import List

import click
import cv2

from officialeye._internal.context.manager import ContextManager
from officialeye._internal.io.drivers.run import RunIODriver
from officialeye._internal.io.drivers.test import TestIODriver
from officialeye._internal.logger.singleton import get_logger
from officialeye.meta import OFFICIALEYE_GITHUB, OFFICIALEYE_VERSION
from officialeye._internal.template.analyze import do_analyze
from officialeye._internal.template.create import create_example_template_config_file
from officialeye._internal.template.schema.loader import load_template

_context_manager: ContextManager = ContextManager()


@click.group()
@click.option("-d", "--debug", is_flag=True, show_default=True, default=False, help="Enable debug mode.")
@click.option("--edir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify export directory.")
@click.option("-q", "--quiet", is_flag=True, show_default=True, default=False, help="Disable standard output messages.")
@click.option("-v", "--verbose", is_flag=True, show_default=True, default=False, help="Enable verbose logging.")
@click.option("-dl", "--disable-logo", is_flag=True, show_default=True, default=False, help="Disable the officialeye logo.")
@click.option("-re", "--raw-errors", is_flag=True, show_default=False, default=False, help="Do not handle errors.")
def cli(debug: bool, edir: str, quiet: bool, verbose: bool, disable_logo: bool, raw_errors: bool):
    global _context_manager

    # configure logger
    get_logger().debug_mode = debug
    get_logger().quiet_mode = quiet
    get_logger().verbose_mode = verbose
    get_logger().disable_logo = disable_logo

    # print OfficialEye logo if necessary
    get_logger().logo()

    # configure context manager
    if edir is not None:
        _context_manager.export_directory = edir

    if raw_errors:
        get_logger().warn("Raw error mode enabled. Use this mode only if you know precisely what you are doing!")
        _context_manager.handle_exceptions = False

    # print preliminary warning if necessary
    if get_logger().debug_mode:
        get_logger().warn("Debug mode enabled. Disable for production use to improve performance.")


# noinspection PyShadowingBuiltins
@click.command()
@click.argument("template_path", type=click.Path(exists=False, file_okay=True, readable=True, writable=True))
@click.argument("template_image", type=click.Path(exists=True, file_okay=True, readable=True, writable=False))
@click.option("--id", type=str, show_default=False, default="example", help="Specify the template identifier.")
@click.option("--name", type=str, show_default=False, default="Example", help="Specify the template name.")
@click.option("--force", is_flag=True, show_default=True, default=False, help="Create missing directories and overwrite file.")
def create(template_path: str, template_image: str, id: str, name: str, force: bool):
    """Creates a new template configuration file at the specified path."""
    create_example_template_config_file(template_path, template_image, id, name, force)


@click.command()
@click.argument("template_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.option("--hide-features", is_flag=True, show_default=False, default=False, help="Do not visualize the locations of features.")
@click.option("--hide-keypoints", is_flag=True, show_default=False, default=False, help="Do not visualize the locations of keypoints.")
def show(template_path: str, hide_features: bool, hide_keypoints: bool):
    """Exports template as an image with features visualized."""

    global _context_manager

    with _context_manager as oe_context:
        # setup IO driver
        oe_context.set_io_driver(TestIODriver(oe_context))

        # load template
        template = load_template(oe_context, template_path)

        # render resulting image
        img = template.show(hide_features=hide_features, hide_keypoints=hide_keypoints)

        # show rendered image
        oe_context.get_io_driver().handle_show_result(template, img)


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
@click.option("--show-features", is_flag=True, show_default=False, default=False, help="Visualize the locations of features.")
@click.option("--visualize", is_flag=True, show_default=False, default=False, help="Generate visualizations of intermediate steps.")
def test(target_path: str, template_paths: List[str], workers: int, show_features: bool, visualize: bool):
    """Visualizes the analysis of an image using one or more templates."""

    global _context_manager

    _context_manager.visualization_generation = visualize

    if _context_manager.visualization_generation:
        get_logger().warn("Visualization generation mode enabled. Disable for production use to improve performance.")

    with _context_manager as oe_context:

        # setup IO driver
        io_driver = TestIODriver(oe_context)
        io_driver.visualize_features = show_features
        oe_context.set_io_driver(io_driver)

        # load target image
        target = cv2.imread(target_path, cv2.IMREAD_COLOR)

        # load templates
        templates = [load_template(oe_context, template_path) for template_path in template_paths]

        # perform analysis
        do_analyze(oe_context, target, templates, num_workers=workers)


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
@click.option("--visualize", is_flag=True, show_default=False, default=False, help="Generate visualizations of intermediate steps.")
def run(target_path: str, template_paths: List[str], workers: int, visualize: bool):
    """Applies one or more templates to an image."""

    global _context_manager

    _context_manager.visualization_generation = visualize

    if _context_manager.visualization_generation:
        get_logger().warn("Visualization generation mode enabled. Disable for production use to improve performance.")

    with _context_manager as oe_context:
        # setup IO driver
        oe_context.set_io_driver(RunIODriver(oe_context))

        # load target image
        target = cv2.imread(target_path, cv2.IMREAD_COLOR)

        # load templates
        templates = [load_template(oe_context, template_path) for template_path in template_paths]

        # perform analysis
        do_analyze(oe_context, target, templates, num_workers=workers)


@click.command()
def homepage():
    """Go to the officialeye's official GitHub homepage."""
    get_logger().info(f"Opening {OFFICIALEYE_GITHUB}")
    click.launch(OFFICIALEYE_GITHUB)


@click.command()
def version():
    """Print the version of OfficialEye."""
    get_logger().info(f"Version: {OFFICIALEYE_VERSION}")


cli.add_command(create)
cli.add_command(show)
cli.add_command(test)
cli.add_command(run)
cli.add_command(homepage)
cli.add_command(version)

if __name__ == "__main__":
    cli()
