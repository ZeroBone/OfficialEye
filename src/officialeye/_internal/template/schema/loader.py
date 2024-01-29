import strictyaml as yml

# noinspection PyProtectedMember
from officialeye._api.feedback.verbosity import Verbosity
from officialeye._internal.context.singleton import get_internal_afi
from officialeye.error.errors.template import ErrTemplateInvalidSyntax

from officialeye._internal.template.schema.schema import generate_template_schema
from officialeye._internal.template.template import Template

_oe_template_schema = generate_template_schema()


def _strict_yaml_error_to_syntax_error(error: yml.YAMLError, /, *, path: str) -> ErrTemplateInvalidSyntax:

    return ErrTemplateInvalidSyntax(
        f"while loading template configuration file at '{path}'.",
        "Could not parse the configuration file due to invalid syntax or encoding.",
        str(error).replace("<unicode string>", path)
    )


def load_template(path: str, /) -> Template:
    """
    Loads a template from a file located at the specified path.

    Arguments:
        path: The path to the YAML template configuration file.

    Returns:
        Loaded template.

    Raises:
        OEError: In case there has been an error validating the correctness of the template.
    """

    global _oe_template_schema

    with open(path, "r") as fh:
        raw_data = fh.read()

    try:
        yaml_document = yml.load(raw_data, schema=_oe_template_schema)
    except yml.YAMLError as err:
        raise _strict_yaml_error_to_syntax_error(err, path=path)

    data = yaml_document.data

    template = Template(data, path)

    get_internal_afi().info(Verbosity.INFO, f"Loaded template: [b]{template}[/]")

    return template
