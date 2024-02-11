from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Iterable, Union

import numpy as np

from officialeye import IMutator

# noinspection PyProtectedMember
from officialeye._api.template.feature import IFeature
from officialeye._internal.context.singleton import get_internal_context
from officialeye._internal.template.feature_class.feature_class import FeatureClass
from officialeye._internal.template.region import InternalRegion
from officialeye._internal.template.utils import load_mutator_from_dict
from officialeye.error.errors.template import ErrTemplateInvalidFeature

if TYPE_CHECKING:
    from officialeye._internal.template.feature_class.manager import FeatureClassManager
    from officialeye.types import FeatureInterpretation


class InternalFeature(InternalRegion, IFeature):

    def __init__(self, template_id: str, feature_dict: Dict[str, any], /):
        super().__init__(template_id, feature_dict)

        if "class" in feature_dict:
            self._class_id = feature_dict["class"]
            assert isinstance(self._class_id, str)
        else:
            self._class_id = None

    def validate_feature_class(self):

        if self._class_id is None:
            return

        feature_classes: FeatureClassManager = self.template.get_feature_classes()

        if not feature_classes.contains_class(self._class_id):
            raise ErrTemplateInvalidFeature(
                f"while loading class for feature '{self.identifier}' in template '{self.template.identifier}'.",
                f"Specified feature class '{self._class_id}' is not defined."
            )

        feature_class = feature_classes.get_class(self._class_id)

        if feature_class.is_abstract():
            raise ErrTemplateInvalidFeature(
                f"while loading class for feature '{self.identifier}' in template '{self.template.identifier}'.",
                f"Cannot instantiate an abstract feature class '{self._class_id}'."
            )

    def get_feature_class(self) -> Union[FeatureClass, None]:
        """ Returns class of feature, or None if the feature does not have a class. """

        if self._class_id is None:
            return None

        feature_classes: FeatureClassManager = self.template.get_feature_classes()

        assert feature_classes.contains_class(self._class_id)

        feature_class = feature_classes.get_class(self._class_id)

        assert not feature_class.is_abstract()

        return feature_class

    def get_mutators(self) -> Iterable[IMutator]:

        feature_class = self.get_feature_class()

        if feature_class is None:
            return []

        mutators = feature_class.get_data()["mutators"]

        assert isinstance(mutators, list)

        return [
            load_mutator_from_dict(mutator_dict) for mutator_dict in mutators
        ]

    def interpret_image(self, img: np.ndarray, /) -> FeatureInterpretation:
        """
        Takes an image and runs the interpretation method defined in the corresponding feature class.
        Assumes that the feature class is present.

        Arguments:
            img: The image which should be passed to the intepretation method.

        Returns:
            The result of running the interpretation method on the image.
        """

        feature_class = self.get_feature_class()

        assert feature_class is not None

        interpretation_method_id = feature_class.get_data()["interpretation"]["method"]
        interpretation_method_config = feature_class.get_data()["interpretation"]["config"]

        assert isinstance(interpretation_method_id, str)
        assert isinstance(interpretation_method_config, dict)

        interpretation_method = get_internal_context().get_interpretation(interpretation_method_id, interpretation_method_config)

        return interpretation_method.interpret(img, self)
