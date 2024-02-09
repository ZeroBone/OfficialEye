"""
This module provides a set of functions connecting the API interface with the internal implementation interface.
In other words, the functions of this module form a low-level API that should be called internally in the actual public API.
"""


import cv2
import numpy as np

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import SupervisionResult
from officialeye._internal.context.singleton import get_internal_context
from officialeye._internal.template.schema.loader import load_template
from officialeye._internal.template.template_data import TemplateData
from officialeye.error.errors.io import ErrIOInvalidImage


def template_load(template_path: str, /, **kwargs) -> TemplateData:

    with get_internal_context().setup(**kwargs):
        template = load_template(template_path)
        return template.get_template_data()


def template_detect(template_path: str, /, *, target_path: str, interpretation_target_path: str | None, **kwargs) -> SupervisionResult:

    with get_internal_context().setup(**kwargs):
        template = load_template(template_path)

        target: np.ndarray = cv2.imread(target_path, cv2.IMREAD_COLOR)

        if interpretation_target_path is None:
            interpretation_target = target
        else:
            interpretation_target = cv2.imread(interpretation_target_path, cv2.IMREAD_COLOR)

            if target.shape != interpretation_target.shape:
                raise ErrIOInvalidImage(
                    "while making sure that the target image and the interpretation target images have the same shape.",
                    f"The shapes mismatch. "
                    f"The target image has shape {target.shape}, while the interpretation target image has shape {interpretation_target.shape}."
                )

        return template.detect(target)
