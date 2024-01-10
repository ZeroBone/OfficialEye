import strictyaml as yml

from officialeye.error.errors.template import ErrTemplateInvalidSyntax
from officialeye.template.parser.schema import generate_template_schema
from officialeye.template.template import Template
from officialeye.util.logger import oe_error, oe_info

_oe_template_schema = generate_template_schema()


def _print_error_message(err: yml.StrictYAMLError, template_path: str):

    oe_error("Error ", bold=True, nl=False)

    if err.context is not None:
        oe_error(err.context, prefix=False)
    else:
        oe_error("while parsing", prefix=False)

    if err.context_mark is not None and (
            err.problem is None
            or err.problem_mark is None
            or err.context_mark.name != err.problem_mark.name
            or err.context_mark.line != err.problem_mark.line
            or err.context_mark.column != err.problem_mark.column
    ):
        oe_error(str(err.context_mark).replace("<unicode string>", template_path))

    if err.problem is not None:
        oe_error("Problem", bold=True, nl=False)
        oe_error(f": {err.problem}", prefix=False)

    if err.problem_mark is not None:
        oe_error(str(err.problem_mark).replace("<unicode string>", template_path))


def load_template(path: str) -> Template:
    global _oe_template_schema

    with open(path, "r") as fh:
        raw_data = fh.read()

    try:
        yaml_document = yml.load(raw_data, schema=_oe_template_schema)
    except yml.StrictYAMLError as err:
        _print_error_message(err, path)
        exit(4)
    except yml.YAMLError as err:
        raise ErrTemplateInvalidSyntax(
            f"while loading template configuration file at '{path}'.",
            f"General parsing error. Check the syntax and the encoding of the file.",
            cause=err
        )

    data = yaml_document.data

    template = Template(data, path)

    oe_info(f"Loaded template: ", nl=False)
    oe_info(str(template), prefix=False, bold=True)

    return template
