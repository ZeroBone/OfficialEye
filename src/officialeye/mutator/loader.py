from typing import Dict

from officialeye.error.errors.template import ErrTemplateInvalidMutator
from officialeye.mutator.mutator import Mutator
from officialeye.mutator.mutators.clahe import CLAHEMutator
from officialeye.mutator.mutators.grayscale import GrayscaleMutator
from officialeye.mutator.mutators.non_local_means_denoising import NonLocalMeansDenoisingMutator


def load_mutator(mutator_id: str, config: Dict[str, any], /) -> Mutator:

    if mutator_id == GrayscaleMutator.MUTATOR_ID:
        return GrayscaleMutator(config)

    if mutator_id == NonLocalMeansDenoisingMutator.MUTATOR_ID:
        return NonLocalMeansDenoisingMutator(config)

    if mutator_id == CLAHEMutator.MUTATOR_ID:
        return CLAHEMutator(config)

    raise ErrTemplateInvalidMutator(
        f"while loading mutator '{mutator_id}'.",
        "Unknown mutator id."
    )


def load_mutator_from_dict(mutator_dict: Dict[str, any], /) -> Mutator:

    assert "id" in mutator_dict

    mutator_id = mutator_dict["id"]

    if "config" in mutator_dict:
        mutator_config = mutator_dict["config"]
    else:
        mutator_config = {}

    return load_mutator(mutator_id, mutator_config)
