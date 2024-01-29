# needed to not break type annotations if we are not in type checking mode
from __future__ import annotations

from typing import TYPE_CHECKING, Dict, Union, Callable

from officialeye._api.feedback.abstract import AbstractFeedbackInterface
from officialeye._api.mutator import Mutator
from officialeye.error.error import OEError
from officialeye.error.errors.internal import ErrInternal
from officialeye.error.errors.template import ErrTemplateIdNotUnique, ErrTemplateInvalidMutator

if TYPE_CHECKING:
    from officialeye._internal.io.driver import IODriver
    from officialeye._internal.template.template import Template


class InternalContext:

    def __init__(self, /, *, afi: AbstractFeedbackInterface, mutator_factories: Dict[str, Callable[[Dict[str, any]], Mutator]]):

        assert afi is not None
        assert mutator_factories is not None

        self._afi = afi
        self._mutator_factories = mutator_factories

        # TODO: get rid of IO drivers
        self._io_driver: Union[IODriver, None] = None

        # keys: template ids
        # values: template
        self._loaded_templates: Dict[str, Template] = {}

    def get_afi(self) -> AbstractFeedbackInterface:
        return self._afi

    def visualization_generation_enabled(self) -> bool:
        # TODO: remove this method
        assert False

    def get_mutator(self, mutator_id: str, mutator_config: Dict[str, any], /):

        # TODO: consider caching mutators that have the same id and configuration

        if mutator_id not in self._mutator_factories:
            raise ErrTemplateInvalidMutator(
                f"while searching for mutator '{mutator_id}'.",
                "Unknown mutator id. Has this mutator been properly loaded?"
            )

        factory = self._mutator_factories[mutator_id]

        return factory(mutator_config)

    def add_template(self, template: Template, /):

        if template.template_id in self._loaded_templates:
            raise ErrTemplateIdNotUnique(
                f"while loading template '{template.template_id}'",
                "A template with the same id has already been loaded."
            )

        self._loaded_templates[template.template_id] = template

        try:
            template.validate()
        except OEError as err:
            # rollback the loaded template
            del self._loaded_templates[template.template_id]
            # reraise the cause
            raise err

    def get_template(self, template_id: str, /) -> Template:
        assert template_id in self._loaded_templates, "Unknown template id"
        return self._loaded_templates[template_id]

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
