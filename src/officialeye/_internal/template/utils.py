from typing import Dict

# noinspection PyProtectedMember
from officialeye._api.mutator import IMutator
from officialeye._internal.context.singleton import get_internal_context


def load_mutator_from_dict(mutator_dict: Dict[str, any], /) -> IMutator:

    assert "id" in mutator_dict

    mutator_id = mutator_dict["id"]

    mutator_config = mutator_dict.get("config", {})

    return get_internal_context().get_mutator(mutator_id, mutator_config)
