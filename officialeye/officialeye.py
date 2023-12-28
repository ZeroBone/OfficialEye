from typing import List

import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.error.error import OEError
from officialeye.io.driver_singleton import oe_io_driver
from officialeye.io.drivers.std import StandardIODriver
from officialeye.meta import OFFICIALEYE_GITHUB, OFFICIALEYE_VERSION, print_logo
from officialeye.template.analyze import do_analyze
from officialeye.template.create import create_example_template_config_file
from officialeye.template.parser import load_template
from officialeye.template.show import do_show
from officialeye.util.logger import oe_info, oe_warn, oe_error


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


def _handle_oe_error(error: OEError):
    # during the access of the io driver, it is possible that another error occurs
    # therefore, we need to handle the io errors occurred during the handling of another error

    error_while_accessing_io_driver = None

    try:
        io_driver = oe_io_driver()
    except OEError as err:
        # fallback to the standard io driver
        io_driver = StandardIODriver()
        error_while_accessing_io_driver = err

    io_driver.output_error(error)

    if error_while_accessing_io_driver is not None:
        oe_error("During the handling of the above error, the following error has occurred!")
        io_driver.output_error(error_while_accessing_io_driver)


# noinspection PyShadowingBuiltins
@click.command()
@click.argument("template_path", type=click.Path(exists=False, file_okay=True, readable=True, writable=True))
@click.option("--id", type=str, show_default=False, default="example", help="Specify the template identifier.")
@click.option("--name", type=str, show_default=False, default="Example", help="Specify the template name.")
@click.option("--force", is_flag=True, show_default=True, default=False, help="Create the .")
def create(template_path: str, id: str, name: str, force: bool):
    """Creates a new template configuration file at the specified path."""

    try:
        create_example_template_config_file(template_path, id, name, force)
    except OEError as err:
        _handle_oe_error(err)

    oe_context().dispose()


@click.command()
@click.argument("template_path", type=click.Path(exists=True, file_okay=True, readable=True))
def show(template_path: str):
    """Exports template as an image with features visualized."""
    try:
        template = load_template(template_path)
        do_show(template)
    except OEError as err:
        _handle_oe_error(err)

    oe_context().dispose()


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True)
def analyze(target_path: str, template_paths: List[str], workers: int):
    """Applies one or more templates to an image."""

    # load target image
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)

    try:
        templates = [load_template(template_path) for template_path in template_paths]
        do_analyze(target, templates, num_workers=workers)
    except OEError as err:
        _handle_oe_error(err)

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
cli.add_command(analyze)
cli.add_command(homepage)
cli.add_command(version)

if __name__ == "__main__":
    cli()
