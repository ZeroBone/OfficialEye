import click
import yamale
import yaml
from yamale import YamaleError
from yaml import SafeLoader
from yaml.parser import ParserError

from officialeye.template.template import Template

_OE_TEMPLATE_SCHEMA_DEF = """
version: str(min=1, max=32, matches=r"^[a-zA-Z0-9_.]*$")
id: str(min=1, max=32, matches=r"^[a-zA-Z0-9_]*$")
name: str(min=1, max=64, matches=r"^[a-zA-Z0-9_ ]*$")
source: str(min=1, max=256)
keypoints: map(include("keypoint"), min=1, key=str(min=1, max=32, matches=r"^[a-zA-Z0-9_]*$"))
features: map(include("feature"), min=1, key=str(min=1, max=32, matches=r"^[a-zA-Z0-9_]*$"))
---
keypoint:
  x: int(min=0, max=1000000)
  y: int(min=0, max=1000000)
  w: int(min=1, max=1000000)
  h: int(min=1, max=1000000)
feature:
  x: int(min=0, max=1000000)
  y: int(min=0, max=1000000)
  w: int(min=1, max=1000000)
  h: int(min=1, max=1000000)
"""

# _oe_template_schema_path = os.path.join(os.path.dirname(os.path.realpath(__file__)), "schema.yml")
_oe_template_schema = yamale.make_schema(content=_OE_TEMPLATE_SCHEMA_DEF)


def load_template(path: str) -> Template:
    global _oe_template_schema

    # click.echo(f"Loading template '{click.format_filename(template_name)}'")

    try:
        with open(path) as f:
            raw_data = yaml.load(f, Loader=SafeLoader)
    except ParserError as err:
        error_desc = "\n".join([
            f"    {line}"
            for line in str(err).replace("\r\n", "\n").split("\n")
        ])

        error_text = f"Syntax Error in '{click.format_filename(path)}':\n{error_desc}"

        click.secho(error_text, bg="red", bold=True)
        exit(1)

    yamale_data = [(raw_data, path)]

    try:
        yamale.validate(_oe_template_schema, yamale_data)
    except YamaleError as e:
        error_desc = "\n".join([
            f"    {err}" for result in e.results for err in result.errors
        ])
        error_text = f"Syntax Error in '{click.format_filename(path)}':\n{error_desc}"
        click.secho(error_text, bg="red", bold=True)
        exit(1)

    data = yamale_data[0][0]

    template = Template(data, path)
    click.secho(f"Loaded feature: {template}", fg="green", bold=True)
    return template
