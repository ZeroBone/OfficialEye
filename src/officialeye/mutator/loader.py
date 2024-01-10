from typing import Dict

from officialeye.error.errors.template import ErrTemplateInvalidMutator
from officialeye.mutator.mutator import Mutator
from officialeye.mutator.mutators.grayscale import GrayscaleMutator
from officialeye.mutator.mutators.non_local_means_denoising import NonLocalMeansDenoisingMutator


def load_mutator(mutator_id: str, config: Dict[str, any], /) -> Mutator:

    if mutator_id == GrayscaleMutator.MUTATOR_ID:
        return GrayscaleMutator(config)

    if mutator_id == NonLocalMeansDenoisingMutator.MUTATOR_ID:
        return NonLocalMeansDenoisingMutator(config)

    raise ErrTemplateInvalidMutator(
        f"while loading mutator '{mutator_id}'.",
        "Unknown mutator id."
    )
