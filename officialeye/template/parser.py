import click
import strictyaml as yml
from officialeye.template.template import Template

_oe_template_schema_keypoint_validator = yml.Map({
    "x": yml.Int(),
    "y": yml.Int(),
    "w": yml.Int(),
    "h": yml.Int()
})

_oe_template_schema_feature_validator = yml.Map({
    "x": yml.Int(),
    "y": yml.Int(),
    "w": yml.Int(),
    "h": yml.Int()
})

_oe_template_schema_region_id = yml.Regex(r"^[a-zA-Z0-9_]{1,32}$")

_oe_template_schema = yml.Map({
    "version": yml.Regex(r"^[a-zA-Z0-9_.]{1,64}$"),
    "id": yml.Regex(r"^[a-z_][a-zA-Z0-9_]{,31}$"),
    "name": yml.Regex(r"^[a-zA-Z0-9_]{1,64}$"),
    "source": yml.Str(),
    "keypoints": yml.MapPattern(_oe_template_schema_region_id, _oe_template_schema_keypoint_validator),
    "matching": yml.Map({
        "engine": yml.Regex(r"^[a-zA-Z0-9_]{1,32}$"),
        "constraints": yml.Map({
            yml.Optional("min_weight"): yml.Map({
                "keypoints": yml.UniqueSeq(_oe_template_schema_region_id),
                "bound": yml.Int()
            })
        })
    }),
    "features": yml.MapPattern(yml.Str(), _oe_template_schema_feature_validator)
})


def _print_error_message(err: yml.StrictYAMLError, template_path: str):

    click.secho("Error ", bold=True, nl=False, err=True)

    if err.context is not None:
        click.echo(err.context, err=True)
    else:
        click.echo("while parsing", err=True)

    if err.context_mark is not None and (
            err.problem is None
            or err.problem_mark is None
            or err.context_mark.name != err.problem_mark.name
            or err.context_mark.line != err.problem_mark.line
            or err.context_mark.column != err.problem_mark.column
    ):
        click.echo(str(err.context_mark).replace("<unicode string>", template_path), err=True)

    if err.problem is not None:
        click.secho("Problem", bold=True, nl=False, err=True)
        click.echo(f": {err.problem}")

    if err.problem_mark is not None:
        click.echo(str(err.problem_mark).replace("<unicode string>", template_path), err=True)


def load_template(path: str) -> Template:
    global _oe_template_schema

    with open(path) as fh:
        raw_data = fh.read()

    try:
        yaml_document = yml.load(raw_data, schema=_oe_template_schema)
    except yml.StrictYAMLError as err:
        # click.echo(click.style('ATTENTION', blink=True, bold=True), err=True)
        _print_error_message(err, path)
        exit(4)

    data = yaml_document.data

    template = Template(data, path)
    click.secho(f"Loaded feature: {template}", fg="green", bold=True)
    return template
