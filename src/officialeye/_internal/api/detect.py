from __future__ import annotations

from typing import TYPE_CHECKING

import cv2
import numpy as np

from officialeye._internal.context.singleton import get_internal_context
from officialeye._internal.template.schema.loader import load_template

if TYPE_CHECKING:
    from officialeye._internal.template.external_supervision_result import ExternalSupervisionResult
    from officialeye._internal.template.internal_supervision_result import InternalSupervisionResult


def template_detect(template_path: str, /, *, target_path: str, **kwargs) -> ExternalSupervisionResult:

    from officialeye._internal.template.external_supervision_result import ExternalSupervisionResult

    with get_internal_context().setup(**kwargs):
        template = load_template(template_path)

        target: np.ndarray = cv2.imread(target_path, cv2.IMREAD_COLOR)

        internal_supervision_result: InternalSupervisionResult = template.do_detect(target)

        return ExternalSupervisionResult(internal_supervision_result)
