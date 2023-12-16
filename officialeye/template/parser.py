import click
import yamale
from yamale import YamaleError

from officialeye.template.template import Template

_OE_TEMPLATE_SCHEMA_DEF = """
version: str(min=1, max=32, matches=r"^[a-zA-Z0-9_.]*$")
id: str(min=1, max=32, matches=r"^[a-zA-Z0-9_]*$")
name: str(min=1, max=64, matches=r"^[a-zA-Z0-9_]*$")
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

    """
    with open(path) as f:
        data = yaml.load(f, Loader=SafeLoader)
    """

    yamale_data = yamale.make_data(path)

    try:
        yamale.validate(_oe_template_schema, yamale_data)
    except YamaleError as e:
        print('Validation failed!\n')
        for result in e.results:
            print("Error validating data '%s' with '%s'\n\t" % (result.data, result.schema))
            for error in result.errors:
                print('%s' % error)
        exit(1)

    data = yamale_data[0][0]

    template = Template(data, path)
    click.secho(f"Loaded feature: {template}", fg="green", bold=True)
    return template
