import click
import yaml
from yaml.loader import SafeLoader
import cv2
from officialeye.template import Template


@click.group()
def cli():
    pass


def load_template(path: str) -> Template:
    # click.echo(f"Loading template '{click.format_filename(template_name)}'")

    with open(path) as f:
        data = yaml.load(f, Loader=SafeLoader)

    template = Template(data, path)
    click.secho(f"Loaded feature: {template}", fg="green", bold=True)
    return template


@click.command()
@click.argument("template_path", type=click.Path(exists=True))
def show(template_path: str):
    template = load_template(template_path)
    template.show()


@click.command()
@click.argument("template_path", type=click.Path(exists=True))
@click.argument("target_path", type=click.Path(exists=True))
def apply(template_path: str, target_path: str):
    template = load_template(template_path)
    target = cv2.imread(target_path, cv2.IMREAD_COLOR)
    template.apply(target)


@click.command()
@click.option('--name', prompt='Identify youself by name')
def analyze(name: str):
    """Describe this tool with colors to You."""
    click.secho(f"Hello {name}", bold=True, bg='green', fg='black')
    click.secho(
        "This is Command Line Interface which gives information of maker named Piyush.", bg='blue', fg='white')


@click.command()
def author():
    """Go to the Author's GitHub"""
    click.launch("https://github.com/ZeroBone")


cli.add_command(show)
cli.add_command(apply)
cli.add_command(author)

if __name__ == "__main__":
    cli()
