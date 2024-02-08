from __future__ import annotations

from typing import TYPE_CHECKING

# noinspection PyProtectedMember
from officialeye._api.template.matcher import IMatcher
# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator
from officialeye._api_builtins.matcher.sift_flann import SiftFlannMatcher

from officialeye._api_builtins.mutator.clahe import CLAHEMutator
from officialeye._api_builtins.mutator.grayscale import GrayscaleMutator
from officialeye._api_builtins.mutator.non_local_means_denoising import NonLocalMeansDenoisingMutator
from officialeye._api_builtins.mutator.rotate import RotateMutator
from officialeye._api_builtins.supervisor.combinatorial import CombinatorialSupervisor
from officialeye._api_builtins.supervisor.least_squares_regression import LeastSquaresRegressionSupervisor

if TYPE_CHECKING:
    from officialeye.types import ConfigDict
    # noinspection PyProtectedMember
    from officialeye._api.context import Context
    # noinspection PyProtectedMember
    from officialeye._api.template.supervisor import ISupervisor


# mutator generators

def _gen_mutator_grayscale(config: ConfigDict, /) -> IMutator:
    return GrayscaleMutator(config)


def _gen_mutator_non_local_means_denoising(config: ConfigDict, /) -> IMutator:
    return NonLocalMeansDenoisingMutator(config)


def _gen_mutator_clahe(config: ConfigDict, /) -> IMutator:
    return CLAHEMutator(config)


def _gen_mutator_rotate(config: ConfigDict, /) -> IMutator:
    return RotateMutator(config)


# matcher generators

def _gen_matcher_sift_flann(config: ConfigDict, /) -> IMatcher:
    return SiftFlannMatcher(config)


# supervisor generators
def _gen_supervisor_combinatorial(config: ConfigDict, /) -> ISupervisor:
    return CombinatorialSupervisor(config)


def _gen_supervisor_least_squares_regression(config: ConfigDict, /) -> ISupervisor:
    return LeastSquaresRegressionSupervisor(config)


def initialize_builtins(context: Context, /):

    # register mutators
    context.register_mutator(GrayscaleMutator.MUTATOR_ID, _gen_mutator_grayscale)
    context.register_mutator(NonLocalMeansDenoisingMutator.MUTATOR_ID, _gen_mutator_non_local_means_denoising)
    context.register_mutator(CLAHEMutator.MUTATOR_ID, _gen_mutator_clahe)
    context.register_mutator(RotateMutator.MUTATOR_ID, _gen_mutator_rotate)

    # register matchers
    context.register_matcher(SiftFlannMatcher.MATCHER_ID, _gen_matcher_sift_flann)

    # register supervisors
    context.register_supervisor(CombinatorialSupervisor.SUPERVISOR_ID, _gen_supervisor_combinatorial)
    context.register_supervisor(LeastSquaresRegressionSupervisor.SUPERVISOR_ID, _gen_supervisor_combinatorial)
