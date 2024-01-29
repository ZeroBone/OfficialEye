"""
OfficialEye main entry point.
"""

from typing import List, Union

import click
import cv2

from officialeye.__version__ import __version__, __github_url__, __github_full_url__
from officialeye._cli.context import CLIContext
from officialeye._cli.run import do_run
from officialeye._cli.show import do_show
from officialeye._cli.ui import Verbosity

# TODO: get rid of all imports from _internal
from officialeye._internal.io.drivers.run import RunIODriver
from officialeye._internal.io.drivers.test import TestIODriver
from officialeye._internal.template.analyze import do_analyze
from officialeye._internal.template.create import create_example_template_config_file
from officialeye._internal.template.schema.loader import load_template


_context = CLIContext()


@click.group()
@click.option("-d", "--debug", is_flag=True, show_default=True, default=False, help="Enable debug mode.")
@click.option("--edir", type=click.Path(exists=True, file_okay=True, readable=True), help="Specify export directory.")
@click.option("-q", "--quiet", is_flag=True, show_default=True, default=False, help="Disable standard output messages.")
@click.option("-v", "--verbose", is_flag=True, show_default=True, default=False, help="Enable verbose logging.")
@click.option("-dl", "--disable-logo", is_flag=True, show_default=True, default=False, help="Disable the officialeye logo.")
@click.option("-re", "--raw-errors", is_flag=True, show_default=False, default=False, help="Do not handle errors.")
def main(debug: bool, edir: str, quiet: bool, verbose: bool, disable_logo: bool, raw_errors: bool):
    global _context

    # configure context
    if quiet:
        verbosity = Verbosity.QUIET
    elif debug:
        if verbose:
            verbosity = Verbosity.DEBUG_VERBOSE
        else:
            verbosity = Verbosity.DEBUG
    else:
        # info verbosity
        if verbose:
            verbosity = Verbosity.INFO_VERBOSE
        else:
            verbosity = Verbosity.INFO

    _context.set_params(
        export_directory=edir,
        handle_exceptions=not raw_errors,
        verbosity=verbosity,
        disable_logo=disable_logo
    )


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

    global _context

    with _context as context:
        do_show(context, template_path=template_path, hide_features=hide_features, hide_keypoints=hide_keypoints)


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--workers", type=int, default=4, show_default=True, help="Specify number of threads to use for the pool of workers.")
@click.option("--interpret", type=click.Path(exists=True, file_okay=True, readable=True),
              default=None, help="Use the image at the specified path to run the interpretation phase.")
@click.option("--show-features", is_flag=True, show_default=False, default=False, help="Visualize the locations of features.")
@click.option("--visualize", is_flag=True, show_default=False, default=False, help="Generate visualizations of intermediate steps.")
def test(target_path: str, template_paths: List[str], workers: int, interpret: Union[str, None], show_features: bool, visualize: bool):
    """Visualizes the analysis of an image using one or more templates."""

    global _context

    _context.set_params(visualization_generation=visualize)

    with _context as context:
        # print OfficialEye logo and other introductory information (if necessary)
        context.print_intro()
        # TODO

    with (_context_manager as oe_context):

        # setup IO driver
        io_driver = TestIODriver(oe_context)
        io_driver.visualize_features = show_features
        oe_context.set_io_driver(io_driver)

        # load target image
        target = cv2.imread(target_path, cv2.IMREAD_COLOR)

        # load interpretation target image if necessary
        interpretation_target: Union[cv2.Mat, None] = \
            None if interpret is None else cv2.imread(interpret, cv2.IMREAD_COLOR)

        # load templates
        templates = [load_template(oe_context, template_path) for template_path in template_paths]

        # perform analysis
        do_analyze(oe_context, target, templates, num_workers=workers, interpretation_target=interpretation_target)


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
@click.option("--interpret", type=click.Path(exists=True, file_okay=True, readable=True),
              default=None, help="Use the image at the specified path to run the interpretation phase.")
@click.option("--visualize", is_flag=True, show_default=False, default=False, help="Generate visualizations of intermediate steps.")
def run(target_path: str, template_paths: List[str], interpret: Union[str, None], visualize: bool):
    """Applies one or more templates to an image."""

    global _context

    with _context as context:
        do_run(
            context,
            target_path=target_path,
            template_paths=template_paths,
            interpret_path=interpret,
            visualize=visualize
        )

        _context_manager = None
        with _context_manager as oe_context:
            # setup IO driver
            oe_context.set_io_driver(RunIODriver(oe_context))

            # load target image
            target = cv2.imread(target_path, cv2.IMREAD_COLOR)

            # load interpretation target image if necessary
            interpretation_target: Union[cv2.Mat, None] = \
                None if interpret is None else cv2.imread(interpret, cv2.IMREAD_COLOR)

            # load templates
            templates = [load_template(oe_context, template_path) for template_path in template_paths]

            # perform analysis
            do_analyze(oe_context, target, templates, num_workers=workers, interpretation_target=interpretation_target)


@click.command()
def homepage():
    """Go to the officialeye's official GitHub homepage."""
    global _context

    with _context as context:
        context.get_terminal_ui().info(Verbosity.INFO, f"GitHub: [link={__github_full_url__}]{__github_url__}[/link]")

    click.launch(__github_full_url__)


@click.command()
def version():
    """Print the version of OfficialEye."""

    global _context

    with _context as context:
        context.get_terminal_ui().info(Verbosity.INFO, f"Version: {__version__}")


main.add_command(create)
main.add_command(show)
main.add_command(test)
main.add_command(run)
main.add_command(homepage)
main.add_command(version)

if __name__ == "__main__":
    main()
