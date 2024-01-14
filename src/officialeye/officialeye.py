from typing import List

import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error import OEError
from officialeye.io.drivers.run import RunIODriver
from officialeye.io.drivers.test import TestIODriver
from officialeye.meta import OFFICIALEYE_GITHUB, OFFICIALEYE_VERSION, print_logo
from officialeye.template.analyze import do_analyze
from officialeye.template.create import create_example_template_config_file
from officialeye.template.parser.loader import load_template
from officialeye.util.logger import oe_info, oe_warn


@click.group()
@click.option("-d", "--debug", is_flag=True, show_default=True, default=False, help="Enable debug mode.")
@click.option("--dedir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify debug export directory.")
@click.option("--edir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify export directory.")
@click.option("-q", "--quiet", is_flag=True, show_default=True, default=False, help="Disable standard output messages.")
@click.option("-v", "--verbose", is_flag=True, show_default=True, default=False, help="Enable verbose logging.")
@click.option("-dl", "--disable-logo", is_flag=True, show_default=True, default=False, help="Disable the officialeye logo.")
def cli(debug: bool, dedir: str, edir: str, quiet: bool, verbose: bool, disable_logo: bool):

    oe_context().debug_mode = debug
    oe_context().quiet_mode = quiet
    oe_context().verbose_mode = verbose
    oe_context().disable_logo = disable_logo

    oe_context().io_driver = TestIODriver()

    if not quiet and not disable_logo:
        print_logo()

    if dedir is not None:
        oe_context().debug_export_directory = dedir

    if edir is not None:
        oe_context().export_directory = edir

    if oe_context().debug_mode:
        oe_warn("Debug mode enabled. Disable for production use to improve performance.")


# noinspection PyShadowingBuiltins
@click.command()
@click.argument("template_path", type=click.Path(exists=False, file_okay=True, readable=True, writable=True))
@click.argument("template_image", type=click.Path(exists=True, file_okay=True, readable=True, writable=False))
@click.option("--id", type=str, show_default=False, default="example", help="Specify the template identifier.")
@click.option("--name", type=str, show_default=False, default="Example", help="Specify the template name.")
@click.option("--force", is_flag=True, show_default=True, default=False, help="Create missing directories and overwrite file.")
def create(template_path: str, template_image: str, id: str, name: str, force: bool):
    """Creates a new template configuration file at the specified path."""

    try:
        create_example_template_config_file(template_path, template_image, id, name, force)
    except OEError as err:
        oe_context().io_driver.output_error(err)
    finally:
        oe_context().dispose()


@click.command()
@click.argument("template_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.option("--hide-features", is_flag=True, show_default=False, default=False, help="Do not visualize the locations of features.")
@click.option("--hide-keypoints", is_flag=True, show_default=False, default=False, help="Do not visualize the locations of keypoints.")
def show(template_path: str, hide_features: bool, hide_keypoints: bool):
    """Exports template as an image with features visualized."""
    try:
        template = load_template(template_path)
        img = template.show(hide_features=hide_features, hide_keypoints=hide_keypoints)
        oe_context().io_driver.output_show_result(template, img)
    except OEError as err:
        oe_context().io_driver.output_error(err)
    finally:
        oe_context().dispose()


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
@click.option("--show-features", is_flag=True, show_default=False, default=False, help="Visualize the locations of features.")
def test(target_path: str, template_paths: List[str], workers: int, show_features: bool):
    """Visualizes the analysis of an image using one or more templates."""

    assert isinstance(oe_context().io_driver, TestIODriver)
    oe_context().io_driver.visualize_features = show_features

    # load target image
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)

    try:
        templates = [load_template(template_path) for template_path in template_paths]
        do_analyze(target, templates, num_workers=workers)
    except OEError as err:
        oe_context().io_driver.output_error(err)
    finally:
        oe_context().dispose()


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
def run(target_path: str, template_paths: List[str], workers: int):
    """Applies one or more templates to an image."""

    # load target image
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)

    # overwrite the IO driver
    oe_context().io_driver = RunIODriver()

    try:
        templates = [load_template(template_path) for template_path in template_paths]
        do_analyze(target, templates, num_workers=workers)
    except OEError as err:
        oe_context().io_driver.output_error(err)
    finally:
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


cli.add_command(create)
cli.add_command(show)
cli.add_command(test)
cli.add_command(run)
cli.add_command(homepage)
cli.add_command(version)

if __name__ == "__main__":
    cli()
