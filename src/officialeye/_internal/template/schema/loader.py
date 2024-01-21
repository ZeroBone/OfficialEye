import strictyaml as yml

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.template import ErrTemplateInvalidSyntax
from officialeye._internal.logger.singleton import get_logger
from officialeye._internal.template.template import Template
from officialeye._internal.template.schema.schema import generate_template_schema

_oe_template_schema = generate_template_schema()


def _print_error_message(err: yml.StrictYAMLError, template_path: str):

    get_logger().error("Error ", bold=True, nl=False)

    if err.context is not None:
        get_logger().error(err.context, prefix=False)
    else:
        get_logger().error("while parsing", prefix=False)

    if err.context_mark is not None and (
            err.problem is None
            or err.problem_mark is None
            or err.context_mark.name != err.problem_mark.name
            or err.context_mark.line != err.problem_mark.line
            or err.context_mark.column != err.problem_mark.column
    ):
        get_logger().error(str(err.context_mark).replace("<unicode string>", template_path))

    if err.problem is not None:
        get_logger().error("Problem", bold=True, nl=False)
        get_logger().error(f": {err.problem}", prefix=False)

    if err.problem_mark is not None:
        get_logger().error(str(err.problem_mark).replace("<unicode string>", template_path))


def load_template(context: Context, path: str) -> Template:
    """
    Loads a template from a file located at the specified path.

    Arguments:
        context: The global officialeye context.
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
    except yml.StrictYAMLError as err:
        _print_error_message(err, path)
        exit(4)
    except yml.YAMLError:
        raise ErrTemplateInvalidSyntax(
            f"while loading template configuration file at '{path}'.",
            f"General parsing error. Check the syntax and the encoding of the file."
        )

    data = yaml_document.data

    template = Template(context, data, path)

    get_logger().info(f"Loaded template: ", nl=False)
    get_logger().info(str(template), prefix=False, bold=True)

    return template
