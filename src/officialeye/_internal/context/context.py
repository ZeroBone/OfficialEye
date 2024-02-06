# needed to not break type annotations if we are not in type checking mode
from __future__ import annotations

from types import TracebackType
from typing import TYPE_CHECKING, Dict, Union, Callable

from officialeye._internal.feedback.abstract import AbstractFeedbackInterface
from officialeye._internal.feedback.dummy import DummyFeedbackInterface
from officialeye.error.error import OEError
from officialeye.error.errors.internal import ErrInternal
from officialeye.error.errors.template import ErrTemplateIdNotUnique, ErrTemplateInvalidMutator, ErrTemplateInvalidMatchingEngine

if TYPE_CHECKING:
    # noinspection PyProtectedMember
    from officialeye._api.template.match import Matcher
    # noinspection PyProtectedMember
    from officialeye._api.mutator import Mutator
    from officialeye._internal.io.driver import IODriver
    from officialeye._internal.template.template import Template
    from officialeye.types import ConfigDict


class InternalContext:

    def __init__(self):
        self._afi = DummyFeedbackInterface()

        self._mutator_factories: Dict[str, Callable[[ConfigDict], Mutator]] = {}
        self._matcher_factories: Dict[str, Callable[[ConfigDict], Matcher]] = {}

        # TODO: get rid of IO drivers
        self._io_driver: Union[IODriver, None] = None

        # keys: template ids
        # values: template
        self._loaded_templates: Dict[str, Template] = {}

        # keys: paths to templates
        # values: corresponding template ids
        self._template_ids: Dict[str, str] = {}

    def setup(self, /, *, afi: AbstractFeedbackInterface, mutator_factories: Dict[str, Callable[[ConfigDict], Mutator]],
              matcher_factories: Dict[str, Callable[[ConfigDict], Matcher]]) -> InternalContext:
        assert afi is not None
        assert mutator_factories is not None

        self._afi = afi
        self._mutator_factories = mutator_factories
        self._matcher_factories = matcher_factories

        return self

    def __enter__(self):
        return None

    def __exit__(self, exception_type: any, exception_value: BaseException, traceback: TracebackType):
        # inform the parent process that the current task is done
        self._afi.dispose()
        self._afi = DummyFeedbackInterface()

    def get_afi(self) -> AbstractFeedbackInterface:
        return self._afi

    def visualization_generation_enabled(self) -> bool:
        # TODO: remove this method
        assert False

    def get_mutator(self, mutator_id: str, mutator_config: ConfigDict, /) -> Mutator:

        # TODO: (low priority) consider caching mutators that have the same id and configuration

        if mutator_id not in self._mutator_factories:
            raise ErrTemplateInvalidMutator(
                f"while loading mutator '{mutator_id}'.",
                "Unknown mutator. Has this mutator been properly loaded?"
            )

        return self._mutator_factories[mutator_id](mutator_config)

    def get_matcher(self, matcher_id: str, matcher_config: ConfigDict, /) -> Matcher:

        # TODO: (low priority) consider caching matchers that have the same id and configuration

        if matcher_id not in self._matcher_factories:
            raise ErrTemplateInvalidMatchingEngine(
                f"while loading matcher '{matcher_id}'.",
                "Unknown matcher. Has this matcher been properly loaded?"
            )

        return self._matcher_factories[matcher_id](matcher_config)

    def add_template(self, template: Template, /):

        template_path = template.get_path()

        assert template_path not in self._template_ids, "A template from the same path has already been loaded"

        if template.template_id in self._loaded_templates:
            raise ErrTemplateIdNotUnique(
                f"while loading template '{template.template_id}'",
                "A template with the same id has already been loaded."
            )

        self._loaded_templates[template.template_id] = template
        self._template_ids[template_path] = template.template_id

        try:
            template.validate()
        except OEError as err:
            # rollback the loaded template
            del self._loaded_templates[template.template_id]
            del self._template_ids[template_path]

            # reraise the cause
            raise err

    def get_template(self, template_id: str, /) -> Template:
        assert template_id in self._loaded_templates, "Unknown template id"
        return self._loaded_templates[template_id]

    def get_template_by_path(self, template_path: str, /) -> Template | None:

        if template_path not in self._template_ids:
            return None

        template_id = self._template_ids[template_path]

        return self.get_template(template_id)

    # TODO: reconsider the need of all methods beyond this point

    def get_io_driver(self) -> IODriver:

        if self._io_driver is None:
            raise ErrInternal(
                "while trying to access officialeye's IO driver.",
                "The present officialeye context does not have an IO Driver set."
            )

        return self._io_driver

    def set_io_driver(self, io_driver: IODriver, /):
        assert io_driver is not None
        self._io_driver = io_driver
