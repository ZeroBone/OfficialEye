from officialeye.error.errors.template import ErrTemplateInvalidFeatureClass
from officialeye.template.feature_class.manager import FeatureClassManager


def load_template_feature_classes(feature_classes_dict: dict, template_id: str, /) -> FeatureClassManager:

    assert isinstance(feature_classes_dict, dict)

    _manager = FeatureClassManager(template_id)

    for class_id in feature_classes_dict:

        if _manager.contains_class(class_id):
            raise ErrTemplateInvalidFeatureClass(
                f"while loading feature classes of template '{template_id}'.",
                f"Class '{class_id}' has been defined more than once."
            )

        _manager.add_class(class_id, feature_classes_dict[class_id])

    _manager.inline_all_classes()

    return _manager
