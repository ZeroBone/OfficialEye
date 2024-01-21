import strictyaml as yml

from officialeye._internal.diffobject.specification import DiffObjectSpecification
from officialeye._internal.diffobject.specification_entries.boolean import BooleanSpecificationEntry
from officialeye._internal.diffobject.specification_entries.list import ListSpecificationEntry
from officialeye._internal.diffobject.specification_entries.object import ObjectSpecificationEntry
from officialeye._internal.diffobject.specification_entries.string import StringSpecificationEntry

_alphanumeric_id_validator = yml.Regex(r"^[a-zA-Z0-9_]{1,64}$")

_mutator_specification = yml.Map({
    "id": _alphanumeric_id_validator,
    yml.Optional("config"): yml.EmptyDict() | yml.MapPattern(_alphanumeric_id_validator, yml.Any())
})

feature_class_object_specification = DiffObjectSpecification({
    "abstract": BooleanSpecificationEntry(yml.Bool()),
    "inherits": StringSpecificationEntry(_alphanumeric_id_validator),
    "mutators": ListSpecificationEntry(yml.EmptyList() | yml.Seq(_mutator_specification)),
    "interpretation": {
        "method": StringSpecificationEntry(_alphanumeric_id_validator),
        "config": ObjectSpecificationEntry(yml.EmptyDict() | yml.MapPattern(_alphanumeric_id_validator, yml.Any()))
    }
})


def generate_template_schema() -> yml.Map:
    global _alphanumeric_id_validator

    _keypoint_validator = yml.Map({
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
        "x": yml.Int(),
        "y": yml.Int(),
        "w": yml.Int(),
        "h": yml.Int(),
        yml.Optional("class"): _alphanumeric_id_validator
    })

    _feature_class_validator = feature_class_object_specification.get_schema()

    return yml.Map({
        "id": _alphanumeric_id_validator,
        "name": yml.Regex(r"^[a-zA-Z0-9_ ']{1,64}$"),
        "source": yml.Str(),
        "mutators": yml.Map({
            "source": yml.EmptyList() | yml.Seq(_mutator_specification),
            "target": yml.EmptyList() | yml.Seq(_mutator_specification)
        }),
        "keypoints": yml.MapPattern(_alphanumeric_id_validator, _keypoint_validator),
        "matching": yml.Map({
            "engine": _alphanumeric_id_validator,
            "config": yml.EmptyDict() | yml.MapPattern(
                _alphanumeric_id_validator,
                yml.EmptyDict() | yml.MapPattern(_alphanumeric_id_validator, yml.Any())
            )
        }),
        "supervision": yml.Map({
            "engine": _alphanumeric_id_validator,
            "config": yml.EmptyDict() | yml.MapPattern(
                _alphanumeric_id_validator,
                yml.EmptyDict() | yml.MapPattern(_alphanumeric_id_validator, yml.Any())
            ),
            "result": yml.Regex(r"^(first|random|best_mse|best_score)$")
        }),
        "feature_classes": yml.MapPattern(_alphanumeric_id_validator, _feature_class_validator),
        "features": yml.MapPattern(_alphanumeric_id_validator, _oe_template_schema_feature_validator)
    })
