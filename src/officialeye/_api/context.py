"""
Module represeting the OfficialEye context.
"""

from __future__ import annotations

from concurrent.futures import Future as PythonFuture
from concurrent.futures import ProcessPoolExecutor
from types import TracebackType
from typing import TYPE_CHECKING, Dict

from officialeye._api.future import Future
from officialeye._api.mutator import IMutator

# noinspection PyProtectedMember
from officialeye._api_builtins.init import initialize_builtins

# noinspection PyProtectedMember
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface

# noinspection PyProtectedMember
from officialeye._internal.feedback.dummy import DummyFeedbackInterface
from officialeye.error.errors.general import ErrInvalidIdentifier
from officialeye.error.errors.internal import ErrInvalidState
from officialeye.error.errors.template import ErrTemplateInvalidMutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict, InterpretationFactory, MatcherFactory, MutatorFactory, SupervisorFactory


class Context:

    def __init__(self, /, *, afi: AbstractFeedbackInterface | None = None):
        self._entered: bool = False
        self._disposed: bool = False

        if afi is None:
            self._afi = DummyFeedbackInterface()
        else:
            self._afi = afi

        self._executor = ProcessPoolExecutor()

        self._mutator_factories: Dict[str, MutatorFactory] = {}
        self._matcher_factories: Dict[str, MatcherFactory] = {}
        self._supervisor_factories: Dict[str, SupervisorFactory] = {}
        self._interpretation_factories: Dict[str, InterpretationFactory] = {}

        # initialize with built-in mutators
        initialize_builtins(self)

    def _get_afi(self) -> AbstractFeedbackInterface:
        return self._afi

    def _submit_task(self, task, description: str, *args, **kwargs) -> Future:

        afi_fork = self._afi.fork(description)

        python_future: PythonFuture = self._executor.submit(
            task,
            *args,
            **kwargs,
            # Arguments that need to be always passed to the internal implementation when starting tasks.
            # It is very important that the argument dictionary is picklable, because it will be passed from the parent
            # process to a child process by the ProcessPoolExecutor.
            afi=afi_fork,
            mutator_factories=self._mutator_factories,
            matcher_factories=self._matcher_factories,
            supervisor_factories=self._supervisor_factories,
            interpretation_factories=self._interpretation_factories
        )

        return Future(self, python_future, afi_fork=afi_fork)

    def register_mutator(self, mutator_id: str, factory: MutatorFactory, /) -> None:

        if mutator_id in self._mutator_factories:
            raise ErrInvalidIdentifier(
                f"while adding the '{mutator_id}' mutator.",
                "A mutator with the same id has already been registered."
            )

        self._mutator_factories[mutator_id] = factory

    def register_matcher(self, matcher_id: str, factory: MatcherFactory, /) -> None:

        if matcher_id in self._matcher_factories:
            raise ErrInvalidIdentifier(
                f"while adding the '{matcher_id}' matcher.",
                "A matcher with the same id has already been registered."
            )

        self._matcher_factories[matcher_id] = factory

    def register_supervisor(self, supervisor_id: str, factory: SupervisorFactory, /) -> None:

        if supervisor_id in self._matcher_factories:
            raise ErrInvalidIdentifier(
                f"while adding the '{supervisor_id}' matcher.",
                "A supervisor with the same id has already been registered."
            )

        self._supervisor_factories[supervisor_id] = factory

    def register_interpretation(self, interpretation_id: str, factory: InterpretationFactory, /) -> None:

        if interpretation_id in self._interpretation_factories:
            raise ErrInvalidIdentifier(
                f"while adding the '{interpretation_id}' interpretation.",
                "An interpretation with the same id has already been registered."
            )

        self._interpretation_factories[interpretation_id] = factory

    def get_mutator(self, mutator_id: str, config: ConfigDict, /) -> IMutator:

        if mutator_id not in self._mutator_factories:
            raise ErrTemplateInvalidMutator(
                f"while looking for a factory generating mutator '{mutator_id}'.",
                "A mutator with this id has not been registered."
            )

        return self._mutator_factories[mutator_id](config)

    def __enter__(self):

        if self._entered:
            raise ErrInvalidState(
                "while entering the api context.",
                "The context has already been entered, which is illegal state."
            )

        self._entered = True
        return self

    def __exit__(self, exception_type: any, exception_value: BaseException | None, traceback: TracebackType | None):
        assert self._entered
        self._entered = False

        if self._disposed:
            raise ErrInvalidState(
                "while leaving the api context.",
                "The resources have already been disposed."
            )

        self.dispose(exception_type, exception_value, traceback)

    def dispose(self, exception_type: any = None, exception_value: BaseException | None = None, traceback: TracebackType | None = None) -> None:
        self._afi.dispose(exception_type, exception_value, traceback)
        self._executor.shutdown(wait=True)
        self._disposed = True
