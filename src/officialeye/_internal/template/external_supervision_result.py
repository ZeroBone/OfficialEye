from __future__ import annotations

from typing import TYPE_CHECKING, Dict

import numpy as np

# noinspection PyProtectedMember
from officialeye._api.context import Context

# noinspection PyProtectedMember
from officialeye._api.future import Future

# noinspection PyProtectedMember
from officialeye._api.image import Image

# noinspection PyProtectedMember
from officialeye._api.template.match import IMatch

# noinspection PyProtectedMember
from officialeye._api.template.supervision_result import ISupervisionResult
from officialeye._internal.api.interpret import template_interpret
from officialeye._internal.api_implementation import IApiInterfaceImplementation

# noinspection PyProtectedMember
from officialeye._internal.template.external_interpretation_result import ExternalInterpretationResult
from officialeye._internal.template.external_matching_result import ExternalMatchingResult
from officialeye._internal.template.external_template import ExternalTemplate

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.image import IImage
    from officialeye._internal.template.internal_supervision_result import InternalSupervisionResult


class ExternalSupervisionResult(ISupervisionResult, IApiInterfaceImplementation):

    def __init__(self, internal_supervision_result: InternalSupervisionResult, /):
        super().__init__()

        self._context: Context | None = None

        self._template_path = internal_supervision_result.template.get_path()

        self._template = ExternalTemplate(internal_supervision_result.template)
        self._matching_result = ExternalMatchingResult(internal_supervision_result.matching_result, self._template)

        self._score = internal_supervision_result.score
        self._delta = internal_supervision_result.delta
        self._delta_prime = internal_supervision_result.delta_prime
        self._transformation_matrix = internal_supervision_result.transformation_matrix

        # noinspection PyProtectedMember
        self._match_weights: Dict[IMatch, float] = internal_supervision_result.get_match_weights()

    def set_api_context(self, context: Context, /) -> None:
        self._context = context

        # propagate the context further down the hierarchy of objects
        self._template.set_api_context(context)
        self._matching_result.set_api_context(context)

    def clear_api_context(self) -> None:
        self._context = None

        self._template.clear_api_context()
        self._matching_result.clear_api_context()

    @property
    def template(self) -> ExternalTemplate:
        return self._template

    @property
    def matching_result(self) -> ExternalMatchingResult:
        return self._matching_result

    @property
    def score(self) -> float:
        return self._score

    @property
    def delta(self) -> np.ndarray:
        return self._delta

    @property
    def delta_prime(self) -> np.ndarray:
        return self._delta_prime

    @property
    def transformation_matrix(self) -> np.ndarray:
        return self._transformation_matrix

    def interpret_async(self, /, *, target: IImage) -> Future:

        # TODO: this is hacky, maybe use a more clean approach here?
        assert isinstance(target, Image)

        assert self._context is not None, \
            ("The external superivision result has no context information, probably because it has been given to the API user "
             "before the context has been initialized in this object via the 'set_api_context' method, which is incorrect behavior.")

        _api_context = self._context

        self.clear_api_context()

        # noinspection PyProtectedMember
        return _api_context._submit_task(
            template_interpret,
            f"Interpreting [b]{self.template.name}[/]...",
            self._template_path,
            self,
            interpretation_target_path=target._path
        )

    def interpret(self, /, **kwargs) -> ExternalInterpretationResult:
        future = self.interpret_async(**kwargs)
        return future.result()

    def get_match_weight(self, match: IMatch, /) -> float:

        if match in self._match_weights:
            return self._match_weights[match]

        return 1.0
