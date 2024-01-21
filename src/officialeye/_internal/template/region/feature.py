from typing import Union, Dict

import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.template import ErrTemplateInvalidFeature
from officialeye._internal.interpretation.loader import load_interpretation_method
from officialeye._internal.logger.singleton import get_logger
from officialeye._internal.mutation.loader import load_mutator_from_dict
from officialeye._internal.template.feature_class.feature_class import FeatureClass
from officialeye._internal.template.feature_class.manager import FeatureClassManager
from officialeye._internal.template.region.region import TemplateRegion

_FEATURE_RECT_COLOR = (0, 0xff, 0)


class TemplateFeature(TemplateRegion):

    def __init__(self, context: Context, template_id: str, feature_dict: Dict[str, any], /):
        super().__init__(context, template_id, feature_dict)

        if "class" in feature_dict:
            self._class_id = feature_dict["class"]
            assert isinstance(self._class_id, str)
        else:
            self._class_id = None

    def visualize(self, img: cv2.Mat, /):
        return super()._visualize(img, rect_color=_FEATURE_RECT_COLOR)

    def validate_feature_class(self):

        if self._class_id is None:
            return

        feature_classes: FeatureClassManager = self.get_template().get_feature_classes()

        if not feature_classes.contains_class(self._class_id):
            raise ErrTemplateInvalidFeature(
                f"while loading class for feature '{self.region_id}' in template '{self.get_template().template_id}'.",
                f"Specified feature class '{self._class_id}' is not defined."
            )

        feature_class = feature_classes.get_class(self._class_id)

        if feature_class.is_abstract():
            raise ErrTemplateInvalidFeature(
                f"while loading class for feature '{self.region_id}' in template '{self.get_template().template_id}'.",
                f"Cannot instantiate an abstract feature class '{self._class_id}'."
            )

    def get_feature_class(self) -> Union[FeatureClass, None]:
        """ Returns class of feature, or None if the feature does not have a class. """

        if self._class_id is None:
            return None

        feature_classes: FeatureClassManager = self.get_template().get_feature_classes()

        assert feature_classes.contains_class(self._class_id)

        feature_class = feature_classes.get_class(self._class_id)

        assert not feature_class.is_abstract()

        return feature_class

    def apply_mutators_to_image(self, img: cv2.Mat, /) -> cv2.Mat:
        """
        Takes an image and applies the mutators defined in the corresponding feature class.

        Arguments:
            img: The image that should be transformed.

        Returns:
            The resulting image.
        """

        feature_class = self.get_feature_class()

        if feature_class is None:
            return img

        mutators = feature_class.get_data()["mutators"]

        assert isinstance(mutators, list)

        for mutator_dict in mutators:
            mutator = load_mutator_from_dict(mutator_dict)
            get_logger().debug(f"Applying mutator '{mutator.mutator_id}'.")
            img = mutator.mutate(img)

        return img

    def interpret_image(self, img: cv2.Mat, /) -> any:
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

        interpretation_method = load_interpretation_method(self._context, interpretation_method_id, interpretation_method_config)

        return interpretation_method.interpret(img, self._template_id, self.region_id)
