"""
Module represeting the OfficialEye context.
"""
from concurrent.futures import ProcessPoolExecutor, Future
from typing import Dict, Callable, List

from officialeye._api.template.template import Template
from officialeye._api.mutator import Mutator
from officialeye._internal.feedback.abstract import AbstractFeedbackInterface
from officialeye._internal.feedback.dummy import DummyFeedbackInterface

# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.clahe import CLAHEMutator
# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.grayscale import GrayscaleMutator
# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.non_local_means_denoising import NonLocalMeansDenoisingMutator
# noinspection PyProtectedMember
from officialeye._api_builtins.mutator.rotate import RotateMutator

from officialeye.error.errors.internal import ErrInvalidState
from officialeye.error.errors.template import ErrTemplateInvalidMutator


def _gen_mutator_grayscale(config: Dict[str, any], /) -> Mutator:
    return GrayscaleMutator(config)


def _gen_mutator_non_local_means_denoising(config: Dict[str, any], /) -> Mutator:
    return NonLocalMeansDenoisingMutator(config)


def _gen_mutator_clahe(config: Dict[str, any], /) -> Mutator:
    return CLAHEMutator(config)


def _gen_mutator_rotate(config: Dict[str, any], /) -> Mutator:
    return RotateMutator(config)


class Context:

    def __init__(self, /, *, afi: AbstractFeedbackInterface | None = None):
        self._entered: bool = False
        self._disposed: bool = False

        if afi is None:
            self._afi = DummyFeedbackInterface()
        else:
            self._afi = afi

        self._executor = ProcessPoolExecutor()

        self._mutator_factories: Dict[str, Callable[[Dict[str, any]], Mutator]] = {}

        # initialize with built-in mutators
        self.add_mutator(GrayscaleMutator.MUTATOR_ID, _gen_mutator_grayscale)
        self.add_mutator(NonLocalMeansDenoisingMutator.MUTATOR_ID, _gen_mutator_non_local_means_denoising)
        self.add_mutator(CLAHEMutator.MUTATOR_ID, _gen_mutator_clahe)
        self.add_mutator(RotateMutator.MUTATOR_ID, _gen_mutator_rotate)

    def _submit_task(self, task, description: str, *args) -> Future:

        afi_fork = self._afi.fork(description)

        future: Future = self._executor.submit(
            task,
            *args,
            # Arguments that need to be always passed to the internal implementation when starting tasks.
            # It is very important that the argument dictionary is picklable, because it will be passed from the parent
            # process to a child process by the ProcessPoolExecutor.
            afi=afi_fork,
            mutator_factories=self._mutator_factories
        )

        def _on_future_done(f: Future, /):
            self._afi.join(afi_fork, f)

        future.add_done_callback(_on_future_done)

        return future

    def run(self, /, *, target_path: str, templates: List[Template], interpret_path: str | None, visualize: bool):
        pass

    def add_mutator(self, mutator_id: str, factory: Callable[[Dict[str, any]], Mutator], /):

        if mutator_id in self._mutator_factories:
            raise ErrTemplateInvalidMutator(
                f"while adding mutator '{mutator_id}'.",
                "A mutator with the same id has already been added."
            )

        self._mutator_factories[mutator_id] = factory

    def __enter__(self):

        if self._entered:
            raise ErrInvalidState(
                "while entering the api context.",
                "The context has already been entered, which is illegal state."
            )

        self._entered = True
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        assert self._entered
        self._entered = False

        if self._disposed:
            raise ErrInvalidState(
                "while leaving the api context.",
                "The resources have already been disposed."
            )

        self.dispose()

    def dispose(self):
        self._afi.dispose()
        self._executor.shutdown(wait=True)
        self._disposed = True
