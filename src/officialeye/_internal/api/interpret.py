from __future__ import annotations

from typing import TYPE_CHECKING

import cv2

from officialeye._internal.context.singleton import get_internal_context

# noinspection PyProtectedMember
from officialeye._internal.template.external_interpretation_result import ExternalInterpretationResult
from officialeye._internal.template.schema.loader import load_template

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.supervision_result import ISupervisionResult


def template_interpret(template_path: str, supervision_result: ISupervisionResult, /, *,
                       interpretation_target_path: str, **kwargs) -> ExternalInterpretationResult:

    with get_internal_context().setup(**kwargs):

        template = load_template(template_path)

        interpretation_target = cv2.imread(interpretation_target_path, cv2.IMREAD_COLOR)

        # TODO: make sure that the target image and the interpretation target images have the same shape, similar to the following snippet
        """
            if target.shape != interpretation_target.shape:
                raise ErrInvalidImage(
                    "while making sure that the target image and the interpretation target images have the same shape.",
                    f"The shapes mismatch. "
                    f"The target image has shape {target.shape}, while the interpretation target image has shape {interpretation_target.shape}."
                )
        """

        feature_interpretation_dict = {}

        for feature in template.features:

            feature_class = feature.get_feature_class()

            if feature_class is None:
                continue

            feature_img = supervision_result.warp_feature(feature, interpretation_target)
            feature_img_mutated = feature.apply_mutators_to_image(feature_img)
            interpretation = feature.interpret_image(feature_img_mutated)

            feature_interpretation_dict[feature.identifier] = interpretation

        return ExternalInterpretationResult(template, feature_interpretation_dict)
