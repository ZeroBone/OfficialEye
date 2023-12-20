import click
# noinspection PyPackageRequirements
import cv2

from officialeye.context.singleton import oe_context
from officialeye.meta import OFFICIALEYE_GITHUB, OFFICIALEYE_VERSION, print_logo
from officialeye.template.parser import load_template


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

    if not quiet and not disable_logo:
        print_logo()

    if oe_context().debug_mode and not oe_context().quiet_mode:
        click.secho("Warning: Debug mode enabled. Disable for production use to avoid performance issues.",
                    bg="yellow", bold=True)
    if dedir is not None:
        oe_context().debug_export_directory = dedir
    if edir is not None:
        oe_context().export_directory = edir


@click.command()
@click.argument("template_path", type=click.Path(exists=True, file_okay=True, readable=True))
def show(template_path: str):
    """Exports template as an image with features visualized."""
    template = load_template(template_path)
    template.show()
    oe_context().dispose()


@click.command()
@click.argument("target_path", type=click.Path(exists=True, file_okay=True, readable=True))
@click.argument("template_paths", type=click.Path(exists=True, file_okay=True, readable=True), nargs=-1)
def analyze(target_path: str, template_paths: str):
    """Applies one or more templates to an image."""

    # load target image
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)

    # apply the templates to the image
    for template_path in template_paths:
        template = load_template(template_path)
        template.analyze(target, debug_mode=oe_context().debug_mode)

    oe_context().dispose()


@click.command()
def homepage():
    """Go to the officialeye's official GitHub homepage."""
    if not oe_context().quiet_mode:
        click.secho(f"Opening {OFFICIALEYE_GITHUB}", bg="blue", fg="white")
    click.launch(OFFICIALEYE_GITHUB)
    oe_context().dispose()


@click.command()
def version():
    """Go to the officialeye's official GitHub homepage."""
    click.echo(f"Version: v{OFFICIALEYE_VERSION}")
    oe_context().dispose()


cli.add_command(show)
cli.add_command(analyze)
cli.add_command(homepage)
cli.add_command(version)

if __name__ == "__main__":
    cli()
