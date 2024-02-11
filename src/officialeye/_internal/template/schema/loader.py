import strictyaml as yml

from officialeye._internal.context.singleton import get_internal_afi, get_internal_context

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye._internal.template.internal_template import InternalTemplate
from officialeye._internal.template.schema.schema import generate_template_schema
from officialeye.error.errors.template import ErrTemplateInvalidSyntax

_oe_template_schema = generate_template_schema()


def _strict_yaml_error_to_syntax_error(error: yml.YAMLError, /, *, path: str) -> ErrTemplateInvalidSyntax:

    return ErrTemplateInvalidSyntax(
        f"while loading template configuration file at '{path}'.",
        "Could not parse the configuration file due to invalid syntax or encoding.",
        str(error).replace("<unicode string>", path)
    )


def _do_load_template(path: str, /) -> InternalTemplate:
    global _oe_template_schema

    with open(path, "r") as fh:
        raw_data = fh.read()

    try:
        yaml_document = yml.load(raw_data, schema=_oe_template_schema)
    except yml.YAMLError as err:
        raise _strict_yaml_error_to_syntax_error(err, path=path) from err

    data = yaml_document.data

    template = InternalTemplate(data, path)

    get_internal_afi().info(Verbosity.DEBUG, f"Loaded template: [b]{template}[/]")

    return template


def load_template(path: str, /) -> InternalTemplate:
    """
    Loads a template from a file located at the specified path.

    Arguments:
        path: The path to the YAML template configuration file.

    Returns:
        Loaded template.

    Raises:
        OEError: In case there has been an error validating the correctness of the template.
    """

    template = get_internal_context().get_template_by_path(path)

    if template is not None:
        get_internal_afi().info(Verbosity.DEBUG, f"Template at path '{path}' has already been loaded and cached, reusing it!")
        return template

    get_internal_afi().info(Verbosity.DEBUG, f"Template at path '{path}' has not yet been loaded, loading it.")

    return _do_load_template(path)
