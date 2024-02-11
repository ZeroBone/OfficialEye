# needed to not break type annotations if we are not in type checking mode
from __future__ import annotations

from types import TracebackType
from typing import TYPE_CHECKING, Dict

from officialeye._internal.feedback.abstract import AbstractFeedbackInterface
from officialeye._internal.feedback.dummy import DummyFeedbackInterface
from officialeye._internal.feedback.verbosity import Verbosity
from officialeye.error.error import OEError
from officialeye.error.errors.general import ErrInvalidKey
from officialeye.error.errors.template import ErrTemplateIdNotUnique

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    # noinspection PyProtectedMember
    from officialeye._api.mutator import IMutator
    from officialeye._api.template.interpretation import IInterpretation

    # noinspection PyProtectedMember
    from officialeye._api.template.matcher import IMatcher

    # noinspection PyProtectedMember
    from officialeye._api.template.supervisor import ISupervisor
    from officialeye._internal.template.internal_template import InternalTemplate
    from officialeye.types import ConfigDict, InterpretationFactory, MatcherFactory, MutatorFactory, SupervisorFactory


class InternalContext:

    def __init__(self):
        self._afi = DummyFeedbackInterface()

        self._mutator_factories: Dict[str, MutatorFactory] = {}
        self._matcher_factories: Dict[str, MatcherFactory] = {}
        self._supervisor_factories: Dict[str, SupervisorFactory] = {}
        self._interpretation_factories: Dict[str, InterpretationFactory] = {}

        # keys: template ids
        # values: template
        self._loaded_templates: Dict[str, InternalTemplate] = {}

        # keys: paths to templates
        # values: corresponding template ids
        self._template_ids: Dict[str, str] = {}

    def setup(self, /, *, afi: AbstractFeedbackInterface, mutator_factories: Dict[str, MutatorFactory],
              matcher_factories: Dict[str, MatcherFactory], supervisor_factories: Dict[str, SupervisorFactory],
              interpretation_factories: Dict[str, InterpretationFactory]) -> InternalContext:
        assert afi is not None

        assert mutator_factories is not None
        assert matcher_factories is not None
        assert supervisor_factories is not None

        self._afi = afi
        self._mutator_factories = mutator_factories
        self._matcher_factories = matcher_factories
        self._supervisor_factories = supervisor_factories
        self._interpretation_factories = interpretation_factories

        return self

    def __enter__(self):
        return None

    def __exit__(self, exception_type: any, exception_value: BaseException | None, traceback: TracebackType | None):
        # inform the parent process that the current task is done
        self._afi.dispose(exception_type, exception_value, traceback)
        self._afi = DummyFeedbackInterface()

    def get_afi(self) -> AbstractFeedbackInterface:
        return self._afi

    def get_mutator(self, mutator_id: str, mutator_config: ConfigDict, /) -> IMutator:

        # TODO: (low priority) consider caching mutators that have the same id and configuration
        self._afi.info(Verbosity.DEBUG_VERBOSE, f"Loading mutator '{mutator_id}' with configuration {mutator_config}.")

        if mutator_id not in self._mutator_factories:
            raise ErrInvalidKey(
                f"while loading mutator '{mutator_id}'.",
                "Unknown mutator. Has this mutator been properly loaded?"
            )

        return self._mutator_factories[mutator_id](mutator_config)

    def get_matcher(self, matcher_id: str, matcher_config: ConfigDict, /) -> IMatcher:

        # TODO: (low priority) consider caching matchers that have the same id and configuration
        self._afi.info(Verbosity.DEBUG_VERBOSE, f"Loading matcher '{matcher_id}' with configuration {matcher_config}.")

        if matcher_id not in self._matcher_factories:
            raise ErrInvalidKey(
                f"while loading matcher '{matcher_id}'.",
                "Unknown matcher. Has this matcher been properly loaded?"
            )

        return self._matcher_factories[matcher_id](matcher_config)

    def get_supervisor(self, supervisor_id: str, supervisor_config: ConfigDict, /) -> ISupervisor:

        # TODO: (low priority) consider caching supervisors that have the same id and configuration
        self._afi.info(Verbosity.DEBUG_VERBOSE, f"Loading supervisor '{supervisor_id}' with configuration {supervisor_config}.")

        if supervisor_id not in self._supervisor_factories:
            raise ErrInvalidKey(
                f"while loading supervisor '{supervisor_id}'.",
                "Unknown supervisor. Has this supervisor been properly loaded?"
            )

        return self._supervisor_factories[supervisor_id](supervisor_config)

    def get_interpretation(self, interpretation_id: str, interpretation_config: ConfigDict, /) -> IInterpretation:

        # TODO: (low priority) consider caching interpretations that have the same id and configuration
        self._afi.info(Verbosity.DEBUG_VERBOSE, f"Loading interpretation '{interpretation_id}' with configuration {interpretation_config}.")

        if interpretation_id not in self._interpretation_factories:
            raise ErrInvalidKey(
                f"while loading interpretation '{interpretation_id}'.",
                "Unknown interpretation. Has this interpretation method been properly loaded?"
            )

        return self._interpretation_factories[interpretation_id](interpretation_config)

    def add_template(self, template: InternalTemplate, /):

        template_path = template.get_path()

        assert template_path not in self._template_ids, "A template from the same path has already been loaded"

        if template.identifier in self._loaded_templates:
            raise ErrTemplateIdNotUnique(
                f"while loading template '{template.identifier}'",
                "A template with the same id has already been loaded."
            )

        self._loaded_templates[template.identifier] = template
        self._template_ids[template_path] = template.identifier

        try:
            template.validate()
        except OEError as err:
            # rollback the loaded template
            del self._loaded_templates[template.identifier]
            del self._template_ids[template_path]

            # reraise the cause
            raise err

    def get_template(self, template_id: str, /) -> InternalTemplate:
        assert template_id in self._loaded_templates, "Unknown template id"
        return self._loaded_templates[template_id]

    def get_template_by_path(self, template_path: str, /) -> InternalTemplate | None:

        if template_path not in self._template_ids:
            return None

        template_id = self._template_ids[template_path]

        return self.get_template(template_id)
