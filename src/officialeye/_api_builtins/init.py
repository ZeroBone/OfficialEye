from __future__ import annotations

from typing import TYPE_CHECKING

# noinspection PyProtectedMember
from officialeye._api.template.matcher import Matcher
# noinspection PyProtectedMember
from officialeye._api.mutator import Mutator
from officialeye._api_builtins.matcher.sift_flann import SiftFlannMatcher

from officialeye._api_builtins.mutator.clahe import CLAHEMutator
from officialeye._api_builtins.mutator.grayscale import GrayscaleMutator
from officialeye._api_builtins.mutator.non_local_means_denoising import NonLocalMeansDenoisingMutator
from officialeye._api_builtins.mutator.rotate import RotateMutator

if TYPE_CHECKING:
    from officialeye.types import ConfigDict
    # noinspection PyProtectedMember
    from officialeye._api.context import Context


# mutator generators

def _gen_mutator_grayscale(config: ConfigDict, /) -> Mutator:
    return GrayscaleMutator(config)


def _gen_mutator_non_local_means_denoising(config: ConfigDict, /) -> Mutator:
    return NonLocalMeansDenoisingMutator(config)


def _gen_mutator_clahe(config: ConfigDict, /) -> Mutator:
    return CLAHEMutator(config)


def _gen_mutator_rotate(config: ConfigDict, /) -> Mutator:
    return RotateMutator(config)


# matcher generators

def _gen_matcher_sift_flann(config: ConfigDict, /) -> Matcher:
    return SiftFlannMatcher(config)


def initialize_builtins(context: Context, /):

    # register mutators
    context.register_mutator(GrayscaleMutator.MUTATOR_ID, _gen_mutator_grayscale)
    context.register_mutator(NonLocalMeansDenoisingMutator.MUTATOR_ID, _gen_mutator_non_local_means_denoising)
    context.register_mutator(CLAHEMutator.MUTATOR_ID, _gen_mutator_clahe)
    context.register_mutator(RotateMutator.MUTATOR_ID, _gen_mutator_rotate)

    # register matchers
    context.register_matcher(SiftFlannMatcher.MATCHER_ID, _gen_matcher_sift_flann)
