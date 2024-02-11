from __future__ import annotations

from concurrent.futures import ALL_COMPLETED
from typing import TYPE_CHECKING, List

from officialeye._api.future import Future, wait
from officialeye._api.template.supervision_result import ISupervisionResult

# noinspection PyProtectedMember
from officialeye._internal.feedback.verbosity import Verbosity

# noinspection PyProtectedMember
from officialeye._internal.template.external_supervision_result import ExternalSupervisionResult
from officialeye.error.error import OEError
from officialeye.error.errors.internal import ErrInternal
from officialeye.error.errors.supervision import ErrSupervisionCorrespondenceNotFound

if TYPE_CHECKING:
    from officialeye._api.context import Context
    from officialeye._api.image import IImage
    from officialeye._api.template.template_interface import ITemplate


def detect(context: Context, *templates: ITemplate, target: IImage) -> ISupervisionResult:

    futures: List[Future] = [
        template.detect_async(target=target) for template in templates
    ]

    done, not_done = wait(futures, return_when=ALL_COMPLETED)

    if len(not_done) > 0:
        # noinspection PyProtectedMember
        context._get_afi().warn(Verbosity.DEBUG, "Some template analysis futures were not completed.")

    regular_errors: List[OEError] = []

    best_result: ISupervisionResult | None = None
    best_result_score: float = -1.0

    for completed_future in done:

        assert isinstance(completed_future, Future)

        if completed_future.cancelled():
            # noinspection PyProtectedMember
            context._get_afi().warn(Verbosity.DEBUG, "A template analysis future was cancelled.")
            continue

        error = completed_future.exception()

        if error is not None:
            # there has been an error during the execution of the future
            # the cause of the error might have been critical, in which case we should raise an exception immediately,
            # or it might be, for example, due to one of the templates not matching the image at all, which is regular behavior
            # therefore, we need to distinguish between a critical error and a regular one

            if not isinstance(error, OEError):
                err = ErrInternal(
                    "while analyzing target image against multiple templates.",
                    "One of the individual analysis workers has crashed due to an external error."
                )
                err.add_external_cause(error)
                raise err

            assert isinstance(error, OEError)

            if error.is_regular:
                # noinspection PyProtectedMember
                context._get_afi().warn(
                    Verbosity.DEBUG,
                    f"A template analysis worker has returned a regular error {error.code} ({error.code_text})."
                )
                regular_errors.append(error)
                continue

            # we are dealing with a non-regular OfficialEye error
            raise error

        result = completed_future.result()
        assert result is not None
        assert isinstance(result, ExternalSupervisionResult)

        # noinspection PyProtectedMember
        context._get_afi().info(Verbosity.DEBUG, f"Template analysis worker yielded a result with score {result.score}.")

        if result.score > best_result_score:
            best_result_score = result.score
            best_result = result

    if best_result is None:
        error = ErrSupervisionCorrespondenceNotFound(
            "while processing the target image analysis results.",
            "Could not establish correspondence of the image with any of the templates provided."
        )

        for worker_error in regular_errors:
            error.add_cause(worker_error)

        raise error

    return best_result
