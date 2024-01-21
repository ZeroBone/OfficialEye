import os
from typing import Dict

import cv2

from officialeye._internal.context.context import Context
from officialeye._internal.error.errors.template import ErrTemplateInvalidInterpretation
from officialeye._internal.interpretation.method import InterpretationMethod
from officialeye._internal.interpretation.serializable import Serializable


class FileMethod(InterpretationMethod):

    METHOD_ID = "file"

    def __init__(self, context: Context, config_dict: Dict[str, any]):
        super().__init__(context, FileMethod.METHOD_ID, config_dict)

        self._path = self.get_config().get("path")

    def interpret(self, feature_img: cv2.Mat, template_id: str, feature_id: str, /) -> Serializable:

        feature = self._context.get_template(template_id).get_feature(feature_id)

        feature_class_generator = feature.get_feature_class().get_features()

        # check if the generator generates at least two elements
        if sum(1 for _ in zip(range(2), feature_class_generator)) == 2:
            raise ErrTemplateInvalidInterpretation(
                "while applying the '{FileMethod.METHOD_ID}' interpretation method.",
                f"This method cannot be applied if there are at least two features inheriting the feature class defining this method."
            )

        os.makedirs(os.path.dirname(self._path), exist_ok=True)

        cv2.imwrite(self._path, feature_img)

        return None
