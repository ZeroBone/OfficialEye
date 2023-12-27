import strictyaml as yml

from officialeye.template.template import Template
from officialeye.util.logger import oe_error, oe_info

_oe_template_schema_keypoint_validator = yml.Map({
    "x": yml.Int(),
    "y": yml.Int(),
    "w": yml.Int(),
    "h": yml.Int(),
    "matches": yml.Map({
        "min": yml.Int(),
        "max": yml.Int()
    })
})

_oe_template_schema_feature_validator = yml.Map({
    "type": yml.Str(),
    "x": yml.Int(),
    "y": yml.Int(),
    "w": yml.Int(),
    "h": yml.Int()
})

_oe_template_schema_region_id = yml.Regex(r"^[a-zA-Z0-9_]{1,32}$")

_oe_template_schema = yml.Map({
    "version": yml.Regex(r"^[a-zA-Z0-9_.]{1,64}$"),
    "id": yml.Regex(r"^[a-z_][a-zA-Z0-9_]{,31}$"),
    "name": yml.Regex(r"^[a-zA-Z0-9_ ]{1,64}$"),
    "source": yml.Str(),
    "keypoints": yml.MapPattern(_oe_template_schema_region_id, _oe_template_schema_keypoint_validator),
    "matching": yml.Map({
        "engine": yml.Regex(r"^[a-zA-Z0-9_]{1,32}$")
    }),
    "supervision": yml.Map({
        "engine": yml.Regex(r"^[a-zA-Z0-9_]{1,32}$"),
        "config": yml.Map({
            yml.Optional("combinatorial"): yml.Map({
                "min_match_factor": yml.Float(),
                "max_transformation_error": yml.Int(),
                "balance_factor": yml.Int()
            })
        }),
        "result": yml.Regex(r"^(first|random|best_mse|best_score)$")
    }),
    "features": yml.MapPattern(yml.Str(), _oe_template_schema_feature_validator)
})


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

    data = yaml_document.data

    template = Template(data, path)

    oe_info(f"Loaded template: ", nl=False)
    oe_info(str(template), prefix=False, bold=True)

    return template
